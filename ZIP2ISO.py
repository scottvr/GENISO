import os
import sys
import argparse
import zipfile
import struct
import time
import math
from datetime import datetime

# --- Constants & ISO Standards ---
SECTOR_SIZE = 2048
BUFFER_SIZE = 1024 * 64  # 64KB chunks for streaming

# --- Helper Functions for ISO 9660 Byte Packing ---

def to_711(val):
    return struct.pack('B', val)

def to_712(val):
    return struct.pack('b', val)

def to_721(val):
    return struct.pack('<H', val)

def to_722(val):
    return struct.pack('>H', val)

def to_723(val):
    return to_721(val) + to_722(val)

def to_731(val):
    return struct.pack('<I', val)

def to_732(val):
    return struct.pack('>I', val)

def to_733(val):
    return to_731(val) + to_732(val)

def iso_date_long(dt):
    """17-byte ASCII date format for Volume Descriptors."""
    s = dt.strftime('%Y%m%d%H%M%S00').encode('ascii')
    return s + to_712(0)

def iso_date_short(dt):
    """7-byte binary date format for Directory Records."""
    return struct.pack('BBBBBBB',
                       dt.year - 1900, dt.month, dt.day,
                       dt.hour, dt.minute, dt.second, 0)

def pad_sector(data):
    """Pads bytes to the nearest 2048-byte sector boundary."""
    rem = len(data) % SECTOR_SIZE
    if rem == 0:
        return data
    return data + (b'\x00' * (SECTOR_SIZE - rem))

# --- Core Classes ---

class DirectoryEntry:
    def __init__(self, name, is_dir, date, zip_info=None, permissions=0o555):
        self.name = name # Original name
        self.iso_name = self._sanitize_name(name, is_dir)
        self.is_dir = is_dir
        self.date = date
        self.zip_info = zip_info 
        
        if zip_info:
            self.size = zip_info.file_size
        else:
            self.size = 0 
            
        self.children = {} 
        self.lba = 0
        self.permissions = permissions
        self.parent_idx = 1 
        self.idx = 0

    def _sanitize_name(self, name, is_dir):
        """Ensures ISO 9660 Level 2 compliance with proper dot handling."""
        name = name.upper()
        
        if is_dir:
            # Directories generally don't have extensions in ISO 9660
            clean = "".join(c if c.isalnum() or c == '_' else '_' for c in name)
            return clean[:31]
        
        # Split by the LAST dot to separate extension
        parts = name.rsplit('.', 1)
        if len(parts) == 2:
            fname, ext = parts
            fname_clean = "".join(c if c.isalnum() or c == '_' else '_' for c in fname)
            ext_clean = "".join(c if c.isalnum() or c == '_' else '_' for c in ext)
            return f"{fname_clean[:28]}.{ext_clean[:3]}"
        else:
            clean = "".join(c if c.isalnum() or c == '_' else '_' for c in name)
            return clean[:31]

class ISOGenerator:
    def __init__(self, zip_path):
        self.zip_path = zip_path
        self.root = DirectoryEntry('', True, datetime.now()) # Root is empty string
        self.total_sectors = 0
        self.path_table = []
        self.path_table_bytes = b''
        self.root_lba = 0
        self.type_l_lba = 0
        self.type_m_lba = 0
        
        self._scan_zip_structure()

    def _scan_zip_structure(self):
        try:
            with zipfile.ZipFile(self.zip_path, 'r') as zf:
                for info in zf.infolist():
                    path_parts = info.filename.strip('/').split('/')
                    current = self.root
                    for i, part in enumerate(path_parts):
                        is_last = (i == len(path_parts) - 1)
                        is_dir_entry = info.is_dir()
                        
                        if is_last and not is_dir_entry:
                            dt = datetime(*info.date_time)
                            perms = (info.external_attr >> 16) & 0xFFFF
                            if perms == 0: perms = 0o644
                            entry = DirectoryEntry(part, False, dt, zip_info=info, permissions=perms)
                            current.children[part] = entry
                        else:
                            if part not in current.children:
                                dt = datetime(*info.date_time) if is_last else datetime.now()
                                current.children[part] = DirectoryEntry(part, True, dt)
                            current = current.children[part]      
        except zipfile.BadZipFile:
            print(f"Error: '{self.zip_path}' is not a valid zip file.")
            sys.exit(1)
        except FileNotFoundError:
            print(f"Error: File '{self.zip_path}' not found.")
            sys.exit(1)

    def _generate_rock_ridge(self, entry, is_root=False):
        rr_data = bytearray()
        
        # --- NEW: SP Entry (System Use Sharing Protocol) ---
        # This MUST be the first entry in the System Use field of the Root Directory.
        # Signature: 'SP', Length: 7, Version: 1, Check: 0xBEEF, Skip: 0
        if is_root:
            rr_data.extend(b'SP\x07\x01\xBE\xEF\x00')

        # --- PX Entry (POSIX Permissions) ---
        mode = entry.permissions 
        if entry.is_dir: mode |= 0o40000 
        else: mode |= 0o100000 
        
        px = b'PX' + to_711(36 + 4) + to_711(1)
        px += to_733(mode) + to_733(0) + to_733(0) + to_733(0)
        rr_data.extend(px)

        # --- NM Entry (Alternative Name) ---
        # Stores the original Mixed-Case filename
        if not is_root:
            nm_content = entry.name.encode('utf-8')
            nm = b'NM' + to_711(5 + len(nm_content)) + to_711(1) + to_711(0) + nm_content
            rr_data.extend(nm)

        return rr_data

    def _pack_dir_record(self, entry, is_dot=False, is_dotdot=False, parent_entry=None):
        if is_dot:
            target = entry
            name_bytes = b'\x00'
        elif is_dotdot:
            target = parent_entry
            name_bytes = b'\x01'
        else:
            target = entry
            name_bytes = entry.iso_name.encode('ascii') + b';1'

        lba = target.lba
        size = target.size
        
        flags = 0
        if target.is_dir: flags |= 0x02

        date = iso_date_short(target.date)
        
        # Check if this is the Root '.' record to trigger SP generation
        is_root_dot = (is_dot and target == self.root)
        sys_use = self._generate_rock_ridge(target, is_root=is_root_dot)
        
        base_len = 33
        name_len = len(name_bytes)
        record_len = base_len + name_len
        
        pad = 0
        if name_len % 2 == 0:
            pad = 1
            record_len += 1
            
        record_len += len(sys_use)
        if record_len % 2 != 0:
            sys_use += b'\x00'
            record_len += 1

        b = bytearray()
        b.append(record_len)
        b.append(0)
        b.extend(to_733(lba))
        b.extend(to_733(size))
        b.extend(date)
        b.append(flags)
        b.append(0)
        b.append(0)
        b.extend(to_723(1))
        b.append(name_len)
        b.extend(name_bytes)
        if pad: b.append(0)
        b.extend(sys_use)
        return b

    def _layout_structure(self):
        # 1. Breadth-first traversal for Path Table
        queue = [self.root]
        self.root.idx = 1
        path_list = [self.root]
        
        idx_counter = 2
        i = 0
        while i < len(path_list):
            curr = path_list[i]
            sorted_children = sorted(curr.children.values(), key=lambda x: x.iso_name)
            for child in sorted_children:
                if child.is_dir:
                    child.idx = idx_counter
                    idx_counter += 1
                    child.parent_idx = curr.idx
                    path_list.append(child)
            i += 1
        self.path_table = path_list

        # 2. Generate Path Table Bytes
        pt_bytes = bytearray()
        for d in self.path_table:
            if d == self.root: name_b = b'\x00\x00'
            else: name_b = d.iso_name.encode('ascii')
            
            row = bytearray()
            row.append(len(name_b))
            row.append(0)
            row.extend(b'\x00\x00\x00\x00')
            row.extend(struct.pack('<H', d.parent_idx))
            row.extend(name_b)
            if len(name_b) % 2 == 1: row.append(0)
            d.pt_offset = len(pt_bytes)
            pt_bytes.extend(row)
        self.path_table_bytes = pt_bytes

        # 3. Assign LBAs
        cursor = 16 # System Area
        self.pvd_lba = cursor
        cursor += 2 # PVD + Terminator
        
        pt_sectors = math.ceil(len(self.path_table_bytes) / SECTOR_SIZE)
        self.type_l_lba = cursor
        cursor += pt_sectors
        self.type_m_lba = cursor
        cursor += pt_sectors
        
        # Directories
        for d in self.path_table:
            size = 0
            size += len(self._pack_dir_record(d, is_dot=True))
            
            # Find parent for DotDot
            if d == self.root: parent = self.root
            else: parent = next((p for p in self.path_table if p.idx == d.parent_idx), self.root)
            
            size += len(self._pack_dir_record(d, is_dotdot=True, parent_entry=parent)) 
            for child in d.children.values():
                size += len(self._pack_dir_record(child))
            
            sectors = math.ceil(size / SECTOR_SIZE)
            d.size = sectors * SECTOR_SIZE
            d.lba = cursor
            cursor += sectors
            
        # Files
        for d in self.path_table:
            for child in d.children.values():
                if not child.is_dir:
                    child.lba = cursor
                    sectors = math.ceil(child.size / SECTOR_SIZE)
                    cursor += sectors
        self.total_sectors = cursor

    def write(self, output_path):
        self._layout_structure()
        
        with zipfile.ZipFile(self.zip_path, 'r') as zf, open(output_path, 'wb') as f:
            # 1. System Area
            f.write(b'\x00' * (16 * SECTOR_SIZE))
            
            # 2. PVD
            pvd = bytearray()
            pvd.append(1) 
            pvd.extend(b'CD001')
            pvd.append(1) 
            pvd.append(0) 
            pvd.extend(b'GENISO'.ljust(32)) 
            pvd.extend(b'ZIP2ISO'.ljust(32)) 
            pvd.extend(b'\x00' * 8) 
            pvd.extend(to_733(self.total_sectors)) 
            pvd.extend(b'\x00' * 32) 
            pvd.extend(to_723(1)) 
            pvd.extend(to_723(1)) 
            pvd.extend(to_723(SECTOR_SIZE)) 
            pvd.extend(to_733(len(self.path_table_bytes))) 
            pvd.extend(to_731(self.type_l_lba)) 
            pvd.extend(to_731(0)) 
            pvd.extend(to_732(self.type_m_lba)) 
            pvd.extend(to_732(0)) 
            pvd.extend(self._pack_dir_record(self.root, is_dot=True)) # Root Record
            pvd.extend(b'ZIP2ISO'.ljust(128)) 
            pvd.extend(b'ZIP2ISO'.ljust(128)) 
            pvd.extend(b'ZIP2ISO'.ljust(128)) 
            pvd.extend(b'ZIP2ISO'.ljust(128)) 
            pvd.extend(b''.ljust(37, b'\x00')) 
            pvd.extend(b''.ljust(37, b'\x00')) 
            pvd.extend(b''.ljust(37, b'\x00')) 
            now = datetime.now()
            pvd.extend(iso_date_long(now)) 
            pvd.extend(iso_date_long(now)) 
            pvd.extend(iso_date_long(now)) 
            pvd.extend(iso_date_long(now)) 
            pvd.append(1) 
            pvd.append(0) 
            f.write(pad_sector(pvd))
            
            # 3. Terminator
            f.write(pad_sector(b'\xFFCD001\x01'))
            
            # 4. Path Tables
            final_pt = bytearray(self.path_table_bytes)
            for d in self.path_table:
                struct.pack_into('<I', final_pt, d.pt_offset + 2, d.lba)
            f.write(pad_sector(final_pt))
            
            pt_m = bytearray()
            for d in self.path_table:
                 if d == self.root: name_b = b'\x00\x00'
                 else: name_b = d.iso_name.encode('ascii')
                 row = bytearray()
                 row.append(len(name_b))
                 row.append(0)
                 row.extend(struct.pack('>I', d.lba)) 
                 row.extend(struct.pack('>H', d.parent_idx))
                 row.extend(name_b)
                 if len(name_b) % 2 == 1: row.append(0)
                 pt_m.extend(row)
            f.write(pad_sector(pt_m))
            
            # 5. Directories
            for d in self.path_table:
                dir_data = bytearray()
                dir_data.extend(self._pack_dir_record(d, is_dot=True))
                parent = next((p for p in self.path_table if p.idx == d.parent_idx), self.root)
                dir_data.extend(self._pack_dir_record(d, is_dotdot=True, parent_entry=parent))
                for child in d.children.values():
                    dir_data.extend(self._pack_dir_record(child))
                f.write(pad_sector(dir_data))
                
            # 6. Files
            total_files = sum(len([c for c in d.children.values() if not c.is_dir]) for d in self.path_table)
            processed = 0
            print(f"Writing {total_files} files...")
            
            for d in self.path_table:
                for child in d.children.values():
                    if not child.is_dir:
                        processed += 1
                        # Simple Progress Indicator
                        sys.stdout.write(f"\rProgress: {processed}/{total_files} ({child.name}){' '*20}")
                        sys.stdout.flush()
                        
                        with zf.open(child.zip_info, 'r') as src:
                            while True:
                                chunk = src.read(BUFFER_SIZE)
                                if not chunk: break
                                f.write(chunk)
                        
                        rem = child.size % SECTOR_SIZE
                        if rem > 0: f.write(b'\x00' * (SECTOR_SIZE - rem))

def main():
    parser = argparse.ArgumentParser(description="Convert ZIP to ISO (Native Python + Rock Ridge)")
    parser.add_argument("input_zip", help="Path to source .zip file")
    parser.add_argument("output_iso", help="Path to destination .iso file")
    args = parser.parse_args()

    print(f"Processing {args.input_zip}...")
    start_time = time.time()
    
    generator = ISOGenerator(args.input_zip)
    generator.write(args.output_iso)
    
    print(f"\n\nSuccess! ISO created at: {args.output_iso}")
    print(f"Time elapsed: {time.time() - start_time:.2f}s")

if __name__ == "__main__":
    main()

