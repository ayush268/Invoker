// Modeled after https://github.com/dafny-lang/libraries/blob/master/src/BoundedInts.dfy

module BoundedInts {
  newtype int8  = x: int  | -0x80 <= x < 0x80
  newtype int16 = x: int  | -0x8000 <= x < 0x8000
  newtype int32 = x: int  | -0x8000_0000 <= x < 0x8000_0000
                                  newtype int64 = x: int  | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

  newtype uint8 = x:int | 0 <= x < 0x100
  newtype uint16 = x:int | 0 <= x < 0x1_0000
  newtype uint32 = x:int | 0 <= x < 0x1_0000_0000
  newtype uint64 = x:i


  type byte = uint8
  type bytes = seq<byte>
}
