use byteorder::ReadBytesExt;
use std::io::{Error, ErrorKind, Read};

fn unsigned_num<R: Read + ?Sized>(n: u32, r: &mut R) -> Result<u128, Error> {
    let x = r.read_u8()? as u128;

    if x < 128 && x < 2u128.pow(n) {
        Ok(x)
    } else if x >= 128 && n > 7 {
        Ok(unsigned_num(n - 7, r)? * 128 + x - 128)
    } else {
        Err(Error::new(ErrorKind::InvalidInput, "unsigned_num"))
    }
}

fn signed_num<R: Read + ?Sized>(n: u32, r: &mut R) -> Result<i128, Error> {
    let x = r.read_u8()? as i128;
    if x < 64 && x < 2i128.pow((n - 1) as u32) {
        Ok(x)
    } else if 64 <= x
        && x < 128
        && (n >= 8 /* avoid panic */ || 128 - 2i128.pow((n - 1) as u32) <= x)
    {
        Ok(x - 2i128.pow(7))
    } else if x >= 128 && n > 7 {
        Ok(signed_num(n - 7, r)? * 128 + x - 128)
    } else {
        Err(Error::new(ErrorKind::InvalidInput, "signed_num"))
    }
}

pub trait ReadLEB128Ext: Read {
    fn read_u32_leb128(&mut self) -> Result<u32, Error> {
        Ok(unsigned_num(32, self)? as u32)
    }

    fn read_i32_leb128(&mut self) -> Result<u32, Error> {
        Ok(signed_num(32, self)? as i32 as u32)
    }

    fn read_i64_leb128(&mut self) -> Result<u64, Error> {
        Ok(signed_num(64, self)? as i64 as u64)
    }
}

impl<R: Read + ?Sized> ReadLEB128Ext for R {}

#[test]
fn test() {
    use std::io::BufReader;

    let a: u8 = 255;
    assert_eq!(255i64, a as i64);

    // u32
    {
        let buf = vec![0x02];
        let mut r = BufReader::new(buf.as_slice());
        assert_eq!(r.read_u32_leb128().unwrap(), 2);
    }

    {
        let buf = vec![0x80, 0x01];
        let mut r = BufReader::new(buf.as_slice());
        assert_eq!(r.read_u32_leb128().unwrap(), 128);
    }

    {
        let buf = vec![0xb9, 0x64];
        let mut r = BufReader::new(buf.as_slice());
        assert_eq!(r.read_u32_leb128().unwrap(), 12857);
    }

    // i32
    {
        let buf = vec![0xff, 0x00];
        let mut r = BufReader::new(buf.as_slice());
        assert_eq!(r.read_i32_leb128().unwrap(), 127);
    }

    {
        let buf = vec![0x7e];
        let mut r = BufReader::new(buf.as_slice());
        assert_eq!(r.read_i32_leb128().unwrap(), -2i32 as u32);
    }

    {
        let buf = vec![0xFE, 0x7F];
        let mut r = BufReader::new(buf.as_slice());
        assert_eq!(r.read_i32_leb128().unwrap(), -2i32 as u32);
    }

    // i64
    {
        let buf = vec![0xff, 0x00];
        let mut r = BufReader::new(buf.as_slice());
        assert_eq!(r.read_i64_leb128().unwrap(), 127);
    }

    {
        let buf = vec![0x7e];
        let mut r = BufReader::new(buf.as_slice());
        assert_eq!(r.read_i64_leb128().unwrap(), -2i64 as u64);
    }

    {
        let buf = vec![0xFE, 0x7F];
        let mut r = BufReader::new(buf.as_slice());
        assert_eq!(r.read_i64_leb128().unwrap(), -2i64 as u64);
    }
}
