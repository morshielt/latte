{-# OPTIONS_GHC -w #-}
{-# OPTIONS -XMagicHash -XBangPatterns -XTypeSynonymInstances -XFlexibleInstances -cpp #-}
#if __GLASGOW_HASKELL__ >= 710
{-# OPTIONS_GHC -XPartialTypeSignatures #-}
#endif
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module ParLatte where
import AbsLatte
import LexLatte
import ErrM
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.8

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
happyIn4 :: (Ident) -> (HappyAbsSyn )
happyIn4 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn4 #-}
happyOut4 :: (HappyAbsSyn ) -> (Ident)
happyOut4 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut4 #-}
happyIn5 :: (Integer) -> (HappyAbsSyn )
happyIn5 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn5 #-}
happyOut5 :: (HappyAbsSyn ) -> (Integer)
happyOut5 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut5 #-}
happyIn6 :: (String) -> (HappyAbsSyn )
happyIn6 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn6 #-}
happyOut6 :: (HappyAbsSyn ) -> (String)
happyOut6 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut6 #-}
happyIn7 :: (Program) -> (HappyAbsSyn )
happyIn7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn7 #-}
happyOut7 :: (HappyAbsSyn ) -> (Program)
happyOut7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut7 #-}
happyIn8 :: (TopDef) -> (HappyAbsSyn )
happyIn8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn ) -> (TopDef)
happyOut8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut8 #-}
happyIn9 :: ([TopDef]) -> (HappyAbsSyn )
happyIn9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn ) -> ([TopDef])
happyOut9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut9 #-}
happyIn10 :: (ClassExt) -> (HappyAbsSyn )
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn ) -> (ClassExt)
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
happyIn11 :: (ClMember) -> (HappyAbsSyn )
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn ) -> (ClMember)
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
happyIn12 :: ([ClMember]) -> (HappyAbsSyn )
happyIn12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn ) -> ([ClMember])
happyOut12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut12 #-}
happyIn13 :: (Arg) -> (HappyAbsSyn )
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn ) -> (Arg)
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
happyIn14 :: ([Arg]) -> (HappyAbsSyn )
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn ) -> ([Arg])
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
happyIn15 :: (Block) -> (HappyAbsSyn )
happyIn15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn ) -> (Block)
happyOut15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut15 #-}
happyIn16 :: ([Stmt]) -> (HappyAbsSyn )
happyIn16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn16 #-}
happyOut16 :: (HappyAbsSyn ) -> ([Stmt])
happyOut16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut16 #-}
happyIn17 :: (Stmt) -> (HappyAbsSyn )
happyIn17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn17 #-}
happyOut17 :: (HappyAbsSyn ) -> (Stmt)
happyOut17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut17 #-}
happyIn18 :: (Item) -> (HappyAbsSyn )
happyIn18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn ) -> (Item)
happyOut18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut18 #-}
happyIn19 :: ([Item]) -> (HappyAbsSyn )
happyIn19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn ) -> ([Item])
happyOut19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut19 #-}
happyIn20 :: (Type) -> (HappyAbsSyn )
happyIn20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn20 #-}
happyOut20 :: (HappyAbsSyn ) -> (Type)
happyOut20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut20 #-}
happyIn21 :: ([Type]) -> (HappyAbsSyn )
happyIn21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn21 #-}
happyOut21 :: (HappyAbsSyn ) -> ([Type])
happyOut21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut21 #-}
happyIn22 :: (Expr) -> (HappyAbsSyn )
happyIn22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn22 #-}
happyOut22 :: (HappyAbsSyn ) -> (Expr)
happyOut22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut22 #-}
happyIn23 :: (Expr) -> (HappyAbsSyn )
happyIn23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn23 #-}
happyOut23 :: (HappyAbsSyn ) -> (Expr)
happyOut23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut23 #-}
happyIn24 :: (ArrSize) -> (HappyAbsSyn )
happyIn24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn24 #-}
happyOut24 :: (HappyAbsSyn ) -> (ArrSize)
happyOut24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut24 #-}
happyIn25 :: (Expr) -> (HappyAbsSyn )
happyIn25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn25 #-}
happyOut25 :: (HappyAbsSyn ) -> (Expr)
happyOut25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut25 #-}
happyIn26 :: (Expr) -> (HappyAbsSyn )
happyIn26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn26 #-}
happyOut26 :: (HappyAbsSyn ) -> (Expr)
happyOut26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut26 #-}
happyIn27 :: (Expr) -> (HappyAbsSyn )
happyIn27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn27 #-}
happyOut27 :: (HappyAbsSyn ) -> (Expr)
happyOut27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut27 #-}
happyIn28 :: (Expr) -> (HappyAbsSyn )
happyIn28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn28 #-}
happyOut28 :: (HappyAbsSyn ) -> (Expr)
happyOut28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut28 #-}
happyIn29 :: (Expr) -> (HappyAbsSyn )
happyIn29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn29 #-}
happyOut29 :: (HappyAbsSyn ) -> (Expr)
happyOut29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut29 #-}
happyIn30 :: (Expr) -> (HappyAbsSyn )
happyIn30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn30 #-}
happyOut30 :: (HappyAbsSyn ) -> (Expr)
happyOut30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut30 #-}
happyIn31 :: (Expr) -> (HappyAbsSyn )
happyIn31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn31 #-}
happyOut31 :: (HappyAbsSyn ) -> (Expr)
happyOut31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut31 #-}
happyIn32 :: ([Expr]) -> (HappyAbsSyn )
happyIn32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn32 #-}
happyOut32 :: (HappyAbsSyn ) -> ([Expr])
happyOut32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut32 #-}
happyIn33 :: (AddOp) -> (HappyAbsSyn )
happyIn33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn33 #-}
happyOut33 :: (HappyAbsSyn ) -> (AddOp)
happyOut33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut33 #-}
happyIn34 :: (MulOp) -> (HappyAbsSyn )
happyIn34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn34 #-}
happyOut34 :: (HappyAbsSyn ) -> (MulOp)
happyOut34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut34 #-}
happyIn35 :: (RelOp) -> (HappyAbsSyn )
happyIn35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn35 #-}
happyOut35 :: (HappyAbsSyn ) -> (RelOp)
happyOut35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut35 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyExpList :: HappyAddr
happyExpList = HappyA# "\x00\x00\x00\x00\x00\x00\x00\x60\x90\x42\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x41\x0a\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x40\x0a\x01\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x08\xa4\x10\x00\x00\x00\x00\x00\x00\x00\x20\x90\x62\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x22\x10\x02\x88\xff\x7b\x00\x00\x00\x00\x80\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x40\x0a\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x40\x00\x00\x00\x00\x00\x40\x02\x01\x00\x00\x00\x00\x00\x00\x00\x00\x10\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x10\x08\x00\x00\x00\x00\x00\x00\x00\x00\x80\x04\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\xec\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x20\x12\x1c\x00\x00\x00\x00\x22\x10\x00\x88\xec\x70\x00\x00\x00\x00\x80\x00\x00\x00\x22\xc1\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x40\x0a\x01\x00\x00\x00\x80\x08\x84\x00\x20\x12\x1c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x88\x40\x00\x00\x22\xc1\x01\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x80\x08\x04\x00\x20\x12\x1c\x00\x00\x00\x00\x00\x00\x00\x08\xa4\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x20\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x02\x01\x00\x88\x04\x07\x00\x00\x00\x80\x08\x04\x00\x20\x12\x1c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x88\x40\x00\x00\x22\xc1\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x08\x04\x00\x20\x12\x1c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x02\x01\x00\x88\x04\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x80\x08\x04\x00\x20\x12\x1c\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x20\x02\x01\x00\x88\x04\x07\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x20\x02\x01\x00\x88\x04\x07\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x88\x40\x00\x00\x22\xc1\x01\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x81\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x01\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x88\x40\x00\x00\x22\xc1\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x22\x10\x02\x88\xff\x73\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x20\x02\x21\x80\xf8\x3f\x07\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x22\x10\x00\x80\x48\x70\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x02\x01\x00\x88\x04\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x20\x02\x01\x00\x88\x04\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x02\x21\x80\xf8\x3f\x07\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x88\x40\x08\x20\xfe\xcf\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pProgram","Ident","Integer","String","Program","TopDef","ListTopDef","ClassExt","ClMember","ListClMember","Arg","ListArg","Block","ListStmt","Stmt","Item","ListItem","Type","ListType","Expr8","Expr7","ArrSize","Expr6","Expr5","Expr4","Expr3","Expr2","Expr1","Expr","ListExpr","AddOp","MulOp","RelOp","'!'","'!='","'%'","'&&'","'('","')'","')null'","'*'","'+'","'++'","','","'-'","'--'","'.'","'/'","':'","';'","'<'","'<='","'='","'=='","'>'","'>='","'['","'[]'","']'","'boolean'","'class'","'else'","'extends'","'false'","'for'","'if'","'int'","'new'","'return'","'string'","'true'","'void'","'while'","'{'","'||'","'}'","L_ident","L_integ","L_quoted","%eof"]
        bit_start = st * 82
        bit_end = (st + 1) * 82
        read_bit = readArrayBit happyExpList
        bits = map read_bit [bit_start..bit_end - 1]
        bits_indexed = zip bits [0..81]
        token_strs_expected = concatMap f bits_indexed
        f (False, _) = []
        f (True, nr) = [token_strs !! nr]

happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\x14\x02\xdc\xff\x00\x00\x00\x00\xdf\xff\x14\x02\x00\x00\xe8\xff\x00\x00\xff\xff\x00\x00\x00\x00\x00\x00\x15\x00\x35\x00\x00\x00\x00\x00\x2e\x02\x18\x00\x13\x00\x00\x00\x00\x00\x3a\x00\x53\x00\xe8\xff\x00\x00\x37\x00\x2e\x02\x2d\x02\x00\x00\xe8\xff\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x2d\x00\x2e\x02\x00\x00\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe8\xff\x8b\x00\xfb\xff\x00\x00\x00\x00\x00\x01\xa7\x00\x60\x00\x41\x00\x5f\x00\x16\x00\x59\x00\x16\x00\x00\x00\x00\x00\x75\x00\x7d\x00\x2e\x02\x5e\x00\x00\x00\x8c\x00\x00\x00\x00\x00\x00\x00\x88\x00\x94\x00\x00\x00\x77\x00\x00\x00\x4e\x00\x88\x00\x2e\x02\x00\x00\x04\x00\x97\x00\x00\x00\x00\x00\x88\x00\x88\x00\x00\x00\x88\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x88\x00\x00\x00\x00\x00\x88\x00\x00\x00\x00\x00\x00\x00\x72\x00\x88\x00\xa0\x00\xa1\x00\x88\x00\xb4\x00\xb1\x00\xba\x00\x88\x00\xd3\x00\xbc\x00\xdd\x00\xe4\x00\x00\x00\xbf\x00\x88\x00\xdb\x00\x00\x00\x00\x00\xd6\x00\xe9\x00\x00\x00\x00\x01\x00\x00\xa7\x00\x00\x00\x00\x00\x00\x00\xe8\xff\xeb\x00\x00\x00\x88\x00\x00\x00\x01\x01\x2f\x00\xec\x00\x2f\x00\xfa\x00\x88\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x88\x00\x00\x00\x00\x00\x06\x01\x88\x00\xf0\x00\x00\x00\x00\x00\x2f\x00\x0c\x01\x00\x00\x2f\x00\x00\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\x69\x00\x00\x00\x00\x00\x00\x00\x00\x00\x92\x00\x00\x00\x1d\x01\x00\x00\x1e\x01\x00\x00\x00\x00\x00\x00\x19\x01\x00\x00\x00\x00\x00\x00\x07\x00\x00\x00\x20\x01\x00\x00\x1b\x01\x00\x00\x00\x00\x21\x01\x00\x00\x17\x01\x3d\x00\x61\x00\x00\x00\x24\x01\x00\x00\x00\x00\x00\x00\x1c\x01\xe2\x00\x00\x00\x72\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf3\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x01\x0e\x01\x0a\x01\x00\x00\x00\x00\x9a\x00\x6e\x01\xd4\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\x00\x78\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x94\x01\x00\x00\x00\x00\x00\x00\x00\x00\x25\x01\x9e\x01\x83\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xba\x01\x8e\x00\x00\x00\x2c\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x03\x00\x00\x00\x00\x00\x36\x00\x00\x00\x00\x00\x00\x00\x2e\x01\xc4\x01\x00\x00\x00\x00\xe0\x01\x00\x00\x00\x00\x00\x00\xa8\x00\x00\x00\x2f\x01\x00\x00\x00\x00\x00\x00\xf6\x00\xea\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1f\x01\x00\x00\x22\x01\x00\x00\x00\x00\x00\x00\x3b\x01\x00\x00\x00\x00\x06\x02\x00\x00\x00\x00\xfe\x00\x00\x00\x1a\x01\x00\x00\xb7\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc5\x00\x00\x00\x00\x00\x00\x00\x10\x02\x00\x00\x00\x00\x00\x00\x36\x01\x00\x00\x00\x00\x52\x01\x00\x00\x00\x00\x00\x00"#

happyAdjustOffset :: Happy_GHC_Exts.Int# -> Happy_GHC_Exts.Int#
happyAdjustOffset off = off

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\x00\x00\x00\x00\xfe\xff\xd7\xff\x00\x00\xf8\xff\xfb\xff\x00\x00\xd4\xff\x00\x00\xd6\xff\xd5\xff\xd3\xff\xf6\xff\x00\x00\xd8\xff\xf7\xff\xef\xff\x00\x00\x00\x00\xf5\xff\xf2\xff\xee\xff\x00\x00\x00\x00\xf0\xff\x00\x00\xef\xff\x00\x00\xf1\xff\x00\x00\xf9\xff\xed\xff\xfa\xff\xeb\xff\x00\x00\x00\x00\xef\xff\xf4\xff\xcf\xff\xc4\xff\xc1\xff\xe8\xff\xea\xff\x00\x00\xc8\xff\xc0\xff\xbd\xff\xbb\xff\xb9\xff\xb7\xff\xb5\xff\xb3\xff\x00\x00\x00\x00\x00\x00\x00\x00\xe9\xff\xc2\xff\x00\x00\x00\x00\x00\x00\x00\x00\xc3\xff\x00\x00\xec\xff\xfd\xff\xfc\xff\x00\x00\xcf\xff\xc8\xff\x00\x00\xe2\xff\xc6\xff\x00\x00\x00\x00\xbf\xff\x00\x00\x00\x00\xbe\xff\xde\xff\x00\x00\x00\x00\xa5\xff\x00\x00\xaa\xff\xa9\xff\xa6\xff\xa8\xff\xa7\xff\x00\x00\xaf\xff\xae\xff\x00\x00\xab\xff\xad\xff\xac\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xdc\xff\xda\xff\x00\x00\xb2\xff\x00\x00\x00\x00\xb1\xff\x00\x00\xe7\xff\x00\x00\x00\x00\x00\x00\xe4\xff\xe5\xff\x00\x00\xce\xff\xbc\xff\xba\xff\xb6\xff\xb8\xff\xb4\xff\xcc\xff\xc5\xff\x00\x00\x00\x00\xc9\xff\x00\x00\xe3\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb2\xff\xcd\xff\xe6\xff\xdb\xff\xd9\xff\xca\xff\xb2\xff\xf3\xff\xb0\xff\x00\x00\x00\x00\xe1\xff\xc7\xff\xdf\xff\x00\x00\x00\x00\xcb\xff\x00\x00\xe0\xff\xdd\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x19\x00\x01\x00\x00\x00\x01\x00\x02\x00\x05\x00\x00\x00\x2c\x00\x0e\x00\x05\x00\x07\x00\x07\x00\x0c\x00\x2f\x00\x00\x00\x09\x00\x0a\x00\x11\x00\x18\x00\x2c\x00\x12\x00\x13\x00\x10\x00\x15\x00\x16\x00\x17\x00\x05\x00\x1b\x00\x19\x00\x19\x00\x10\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2c\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x01\x00\x2c\x00\x05\x00\x1e\x00\x05\x00\x1f\x00\x00\x00\x01\x00\x02\x00\x23\x00\x05\x00\x0c\x00\x26\x00\x00\x00\x11\x00\x2c\x00\x11\x00\x29\x00\x2c\x00\x2d\x00\x2e\x00\x0b\x00\x09\x00\x0a\x00\x12\x00\x13\x00\x1b\x00\x15\x00\x16\x00\x10\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x06\x00\x01\x00\x2c\x00\x2d\x00\x2e\x00\x05\x00\x01\x00\x29\x00\x00\x00\x02\x00\x05\x00\x04\x00\x0c\x00\x18\x00\x19\x00\x07\x00\x00\x00\x0c\x00\x2a\x00\x03\x00\x04\x00\x05\x00\x11\x00\x11\x00\x10\x00\x12\x00\x13\x00\x1b\x00\x15\x00\x16\x00\x17\x00\x1f\x00\x10\x00\x05\x00\x22\x00\x23\x00\x1f\x00\x25\x00\x26\x00\x27\x00\x23\x00\x05\x00\x00\x00\x26\x00\x2c\x00\x2d\x00\x2e\x00\x11\x00\x01\x00\x2c\x00\x2d\x00\x2e\x00\x05\x00\x00\x00\x01\x00\x02\x00\x05\x00\x00\x00\x10\x00\x0c\x00\x0a\x00\x04\x00\x05\x00\x0d\x00\x05\x00\x00\x00\x01\x00\x02\x00\x06\x00\x2c\x00\x14\x00\x12\x00\x13\x00\x10\x00\x15\x00\x16\x00\x17\x00\x18\x00\x1f\x00\x00\x00\x01\x00\x02\x00\x23\x00\x12\x00\x13\x00\x26\x00\x15\x00\x09\x00\x11\x00\x11\x00\x0c\x00\x2c\x00\x2d\x00\x2e\x00\x00\x00\x01\x00\x02\x00\x12\x00\x13\x00\x0b\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x00\x00\x01\x00\x02\x00\x14\x00\x12\x00\x13\x00\x11\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x00\x00\x01\x00\x02\x00\x12\x00\x13\x00\x06\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x00\x00\x01\x00\x02\x00\x29\x00\x12\x00\x13\x00\x0b\x00\x15\x00\x06\x00\x2c\x00\x11\x00\x0b\x00\x05\x00\x0d\x00\x1a\x00\x06\x00\x10\x00\x00\x00\x12\x00\x13\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x00\x00\x01\x00\x02\x00\x0e\x00\x0f\x00\x03\x00\x0e\x00\x0f\x00\x1a\x00\x06\x00\x08\x00\x0b\x00\x10\x00\x0d\x00\x06\x00\x1d\x00\x10\x00\x0f\x00\x12\x00\x13\x00\x06\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x00\x00\x01\x00\x02\x00\x00\x00\x00\x00\x06\x00\x00\x00\x00\x00\x0b\x00\x08\x00\x00\x00\x0b\x00\x1e\x00\x0d\x00\x0c\x00\x1f\x00\x10\x00\x1d\x00\x12\x00\x13\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x00\x00\x01\x00\x02\x00\x14\x00\x0b\x00\x00\x00\xff\xff\x1e\x00\xff\xff\x1d\x00\xff\xff\x0b\x00\xff\xff\x0d\x00\xff\xff\xff\xff\x10\x00\xff\xff\x12\x00\x13\x00\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x0b\x00\xff\xff\x0d\x00\xff\xff\xff\xff\x10\x00\xff\xff\x12\x00\x13\x00\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x00\x00\x01\x00\x02\x00\xff\xff\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\x09\x00\x0a\x00\xff\xff\x10\x00\xff\xff\x12\x00\x13\x00\x10\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x12\x00\x13\x00\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x12\x00\x13\x00\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x12\x00\x13\x00\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x12\x00\x13\x00\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x12\x00\x13\x00\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x12\x00\x13\x00\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x12\x00\x13\x00\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x12\x00\x13\x00\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x12\x00\x13\x00\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x00\x00\x01\x00\x02\x00\x1b\x00\x1c\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x22\x00\xff\xff\xff\xff\x25\x00\xff\xff\x27\x00\xff\xff\xff\xff\x12\x00\x13\x00\x2c\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\xff\xff\x1b\x00\x1b\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x22\x00\x22\x00\xff\xff\x25\x00\x25\x00\x27\x00\x27\x00\xff\xff\xff\xff\x2b\x00\x2c\x00\x2c\x00\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x10\x00\x37\x00\x45\x00\x28\x00\x29\x00\x38\x00\x03\x00\x03\x00\x62\x00\x6a\x00\x7d\x00\xd7\xff\x39\x00\xff\xff\x03\x00\x16\x00\x17\x00\x3a\x00\x63\x00\x03\x00\x46\x00\x2e\x00\x18\x00\x2f\x00\x30\x00\x77\x00\x38\x00\x09\x00\x10\x00\xd7\xff\x49\x00\x3b\x00\x3c\x00\x3d\x00\x0b\x00\x3e\x00\x3f\x00\x0c\x00\x40\x00\x0d\x00\x41\x00\x23\x00\x03\x00\x42\x00\x03\x00\x43\x00\x44\x00\x37\x00\xd7\xff\x26\x00\x14\x00\x38\x00\x3b\x00\x45\x00\x28\x00\x29\x00\x3e\x00\x12\x00\x39\x00\x40\x00\x03\x00\x27\x00\x03\x00\x3a\x00\x16\x00\x03\x00\x43\x00\x44\x00\x1c\x00\x16\x00\x20\x00\x46\x00\x2e\x00\x09\x00\x2f\x00\x76\x00\x18\x00\x3b\x00\x3c\x00\x3d\x00\x0b\x00\x3e\x00\x3f\x00\x0c\x00\x40\x00\x0d\x00\x41\x00\x23\x00\x1b\x00\x37\x00\x03\x00\x43\x00\x44\x00\x38\x00\x37\x00\x23\x00\x03\x00\x54\x00\x38\x00\x55\x00\x39\x00\x81\x00\x10\x00\x1d\x00\x03\x00\x39\x00\x52\x00\x04\x00\x05\x00\x06\x00\x49\x00\x51\x00\x1e\x00\x56\x00\x57\x00\x09\x00\x58\x00\x59\x00\x5a\x00\x3b\x00\x07\x00\x4c\x00\x0b\x00\x3e\x00\x3b\x00\x0c\x00\x40\x00\x0d\x00\x3e\x00\x4b\x00\x03\x00\x40\x00\x03\x00\x43\x00\x44\x00\x82\x00\x37\x00\x03\x00\x43\x00\x44\x00\x38\x00\x45\x00\x28\x00\x29\x00\x45\x00\x03\x00\x7d\x00\x39\x00\x64\x00\x05\x00\x10\x00\x65\x00\x6a\x00\x45\x00\x28\x00\x29\x00\x7c\x00\x03\x00\x66\x00\x46\x00\x2e\x00\x07\x00\x2f\x00\x30\x00\x31\x00\x79\x00\x3b\x00\x45\x00\x28\x00\x29\x00\x3e\x00\x46\x00\x2e\x00\x40\x00\x4f\x00\x5c\x00\x74\x00\x73\x00\x5d\x00\x03\x00\x43\x00\x44\x00\x45\x00\x28\x00\x29\x00\x46\x00\x2e\x00\x70\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x6c\x00\x6d\x00\x45\x00\x28\x00\x29\x00\x71\x00\x46\x00\x2e\x00\x6f\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x6c\x00\x90\x00\x45\x00\x28\x00\x29\x00\x46\x00\x2e\x00\x6c\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x6c\x00\x8f\x00\x27\x00\x28\x00\x29\x00\x23\x00\x46\x00\x2e\x00\x8e\x00\x4c\x00\x8d\x00\x03\x00\x8a\x00\x2a\x00\x88\x00\x2b\x00\x89\x00\x86\x00\x2c\x00\x66\x00\x2d\x00\x2e\x00\x66\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x27\x00\x28\x00\x29\x00\x67\x00\x68\x00\x5f\x00\x67\x00\x8b\x00\x94\x00\x84\x00\x60\x00\x2a\x00\x92\x00\x94\x00\x98\x00\x96\x00\x2c\x00\x61\x00\x2d\x00\x2e\x00\x99\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x27\x00\x28\x00\x29\x00\x0e\x00\x0d\x00\x12\x00\x14\x00\x19\x00\x21\x00\x1c\x00\x24\x00\x2a\x00\x5d\x00\x92\x00\x23\x00\x52\x00\x2c\x00\x5a\x00\x2d\x00\x2e\x00\x75\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x27\x00\x28\x00\x29\x00\x7f\x00\x8e\x00\x86\x00\x00\x00\x5d\x00\x00\x00\x5a\x00\x00\x00\x2a\x00\x00\x00\x99\x00\x00\x00\x00\x00\x2c\x00\x00\x00\x2d\x00\x2e\x00\x00\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x27\x00\x28\x00\x29\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x2a\x00\x00\x00\x9a\x00\x00\x00\x00\x00\x2c\x00\x00\x00\x2d\x00\x2e\x00\x00\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x27\x00\x28\x00\x29\x00\x00\x00\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x45\x00\x28\x00\x29\x00\x16\x00\x6a\x00\x00\x00\x4d\x00\x00\x00\x46\x00\x2e\x00\x18\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x4e\x00\x46\x00\x2e\x00\x00\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x47\x00\x45\x00\x28\x00\x29\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x45\x00\x28\x00\x29\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x46\x00\x2e\x00\x00\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x82\x00\x46\x00\x2e\x00\x00\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x7e\x00\x45\x00\x28\x00\x29\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x45\x00\x28\x00\x29\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x46\x00\x2e\x00\x00\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x7a\x00\x46\x00\x2e\x00\x00\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x74\x00\x45\x00\x28\x00\x29\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x45\x00\x28\x00\x29\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x46\x00\x2e\x00\x00\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x71\x00\x46\x00\x2e\x00\x00\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x8a\x00\x45\x00\x28\x00\x29\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x45\x00\x28\x00\x29\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x46\x00\x2e\x00\x00\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x84\x00\x46\x00\x2e\x00\x00\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x96\x00\x45\x00\x28\x00\x29\x00\x09\x00\x0a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0b\x00\x00\x00\x00\x00\x0c\x00\x00\x00\x0d\x00\x00\x00\x00\x00\x46\x00\x2e\x00\x03\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x78\x00\x00\x00\x09\x00\x09\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0b\x00\x0b\x00\x00\x00\x0c\x00\x0c\x00\x0d\x00\x0d\x00\x00\x00\x00\x00\x20\x00\x03\x00\x03\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (1, 90) [
	(1 , happyReduce_1),
	(2 , happyReduce_2),
	(3 , happyReduce_3),
	(4 , happyReduce_4),
	(5 , happyReduce_5),
	(6 , happyReduce_6),
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32),
	(33 , happyReduce_33),
	(34 , happyReduce_34),
	(35 , happyReduce_35),
	(36 , happyReduce_36),
	(37 , happyReduce_37),
	(38 , happyReduce_38),
	(39 , happyReduce_39),
	(40 , happyReduce_40),
	(41 , happyReduce_41),
	(42 , happyReduce_42),
	(43 , happyReduce_43),
	(44 , happyReduce_44),
	(45 , happyReduce_45),
	(46 , happyReduce_46),
	(47 , happyReduce_47),
	(48 , happyReduce_48),
	(49 , happyReduce_49),
	(50 , happyReduce_50),
	(51 , happyReduce_51),
	(52 , happyReduce_52),
	(53 , happyReduce_53),
	(54 , happyReduce_54),
	(55 , happyReduce_55),
	(56 , happyReduce_56),
	(57 , happyReduce_57),
	(58 , happyReduce_58),
	(59 , happyReduce_59),
	(60 , happyReduce_60),
	(61 , happyReduce_61),
	(62 , happyReduce_62),
	(63 , happyReduce_63),
	(64 , happyReduce_64),
	(65 , happyReduce_65),
	(66 , happyReduce_66),
	(67 , happyReduce_67),
	(68 , happyReduce_68),
	(69 , happyReduce_69),
	(70 , happyReduce_70),
	(71 , happyReduce_71),
	(72 , happyReduce_72),
	(73 , happyReduce_73),
	(74 , happyReduce_74),
	(75 , happyReduce_75),
	(76 , happyReduce_76),
	(77 , happyReduce_77),
	(78 , happyReduce_78),
	(79 , happyReduce_79),
	(80 , happyReduce_80),
	(81 , happyReduce_81),
	(82 , happyReduce_82),
	(83 , happyReduce_83),
	(84 , happyReduce_84),
	(85 , happyReduce_85),
	(86 , happyReduce_86),
	(87 , happyReduce_87),
	(88 , happyReduce_88),
	(89 , happyReduce_89),
	(90 , happyReduce_90)
	]

happy_n_terms = 48 :: Int
happy_n_nonterms = 32 :: Int

happyReduce_1 = happySpecReduce_1  0# happyReduction_1
happyReduction_1 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TV happy_var_1)) -> 
	happyIn4
		 (Ident happy_var_1
	)}

happyReduce_2 = happySpecReduce_1  1# happyReduction_2
happyReduction_2 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TI happy_var_1)) -> 
	happyIn5
		 (read happy_var_1
	)}

happyReduce_3 = happySpecReduce_1  2# happyReduction_3
happyReduction_3 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TL happy_var_1)) -> 
	happyIn6
		 (happy_var_1
	)}

happyReduce_4 = happySpecReduce_1  3# happyReduction_4
happyReduction_4 happy_x_1
	 =  case happyOut9 happy_x_1 of { happy_var_1 -> 
	happyIn7
		 (AbsLatte.Program happy_var_1
	)}

happyReduce_5 = happyReduce 6# 4# happyReduction_5
happyReduction_5 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut20 happy_x_1 of { happy_var_1 -> 
	case happyOut4 happy_x_2 of { happy_var_2 -> 
	case happyOut14 happy_x_4 of { happy_var_4 -> 
	case happyOut15 happy_x_6 of { happy_var_6 -> 
	happyIn8
		 (AbsLatte.FnDef happy_var_1 happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest}}}}

happyReduce_6 = happyReduce 6# 4# happyReduction_6
happyReduction_6 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut4 happy_x_2 of { happy_var_2 -> 
	case happyOut10 happy_x_3 of { happy_var_3 -> 
	case happyOut12 happy_x_5 of { happy_var_5 -> 
	happyIn8
		 (AbsLatte.ClDef happy_var_2 happy_var_3 (reverse happy_var_5)
	) `HappyStk` happyRest}}}

happyReduce_7 = happySpecReduce_1  5# happyReduction_7
happyReduction_7 happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	happyIn9
		 ((:[]) happy_var_1
	)}

happyReduce_8 = happySpecReduce_2  5# happyReduction_8
happyReduction_8 happy_x_2
	happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	case happyOut9 happy_x_2 of { happy_var_2 -> 
	happyIn9
		 ((:) happy_var_1 happy_var_2
	)}}

happyReduce_9 = happySpecReduce_0  6# happyReduction_9
happyReduction_9  =  happyIn10
		 (AbsLatte.NoExt
	)

happyReduce_10 = happySpecReduce_2  6# happyReduction_10
happyReduction_10 happy_x_2
	happy_x_1
	 =  case happyOut4 happy_x_2 of { happy_var_2 -> 
	happyIn10
		 (AbsLatte.Ext happy_var_2
	)}

happyReduce_11 = happySpecReduce_3  7# happyReduction_11
happyReduction_11 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	case happyOut4 happy_x_2 of { happy_var_2 -> 
	happyIn11
		 (AbsLatte.Attr happy_var_1 happy_var_2
	)}}

happyReduce_12 = happyReduce 6# 7# happyReduction_12
happyReduction_12 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut20 happy_x_1 of { happy_var_1 -> 
	case happyOut4 happy_x_2 of { happy_var_2 -> 
	case happyOut14 happy_x_4 of { happy_var_4 -> 
	case happyOut15 happy_x_6 of { happy_var_6 -> 
	happyIn11
		 (AbsLatte.Meth happy_var_1 happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest}}}}

happyReduce_13 = happySpecReduce_0  8# happyReduction_13
happyReduction_13  =  happyIn12
		 ([]
	)

happyReduce_14 = happySpecReduce_2  8# happyReduction_14
happyReduction_14 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut11 happy_x_2 of { happy_var_2 -> 
	happyIn12
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_15 = happySpecReduce_2  9# happyReduction_15
happyReduction_15 happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	case happyOut4 happy_x_2 of { happy_var_2 -> 
	happyIn13
		 (AbsLatte.Arg happy_var_1 happy_var_2
	)}}

happyReduce_16 = happySpecReduce_0  10# happyReduction_16
happyReduction_16  =  happyIn14
		 ([]
	)

happyReduce_17 = happySpecReduce_1  10# happyReduction_17
happyReduction_17 happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	happyIn14
		 ((:[]) happy_var_1
	)}

happyReduce_18 = happySpecReduce_3  10# happyReduction_18
happyReduction_18 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut14 happy_x_3 of { happy_var_3 -> 
	happyIn14
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_19 = happySpecReduce_3  11# happyReduction_19
happyReduction_19 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut16 happy_x_2 of { happy_var_2 -> 
	happyIn15
		 (AbsLatte.Block (reverse happy_var_2)
	)}

happyReduce_20 = happySpecReduce_0  12# happyReduction_20
happyReduction_20  =  happyIn16
		 ([]
	)

happyReduce_21 = happySpecReduce_2  12# happyReduction_21
happyReduction_21 happy_x_2
	happy_x_1
	 =  case happyOut16 happy_x_1 of { happy_var_1 -> 
	case happyOut17 happy_x_2 of { happy_var_2 -> 
	happyIn16
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_22 = happySpecReduce_1  13# happyReduction_22
happyReduction_22 happy_x_1
	 =  happyIn17
		 (AbsLatte.Empty
	)

happyReduce_23 = happySpecReduce_1  13# happyReduction_23
happyReduction_23 happy_x_1
	 =  case happyOut15 happy_x_1 of { happy_var_1 -> 
	happyIn17
		 (AbsLatte.BStmt happy_var_1
	)}

happyReduce_24 = happySpecReduce_3  13# happyReduction_24
happyReduction_24 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	case happyOut19 happy_x_2 of { happy_var_2 -> 
	happyIn17
		 (AbsLatte.Decl happy_var_1 happy_var_2
	)}}

happyReduce_25 = happyReduce 4# 13# happyReduction_25
happyReduction_25 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut22 happy_x_1 of { happy_var_1 -> 
	case happyOut31 happy_x_3 of { happy_var_3 -> 
	happyIn17
		 (AbsLatte.Ass happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_26 = happySpecReduce_3  13# happyReduction_26
happyReduction_26 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	happyIn17
		 (AbsLatte.Incr happy_var_1
	)}

happyReduce_27 = happySpecReduce_3  13# happyReduction_27
happyReduction_27 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	happyIn17
		 (AbsLatte.Decr happy_var_1
	)}

happyReduce_28 = happySpecReduce_3  13# happyReduction_28
happyReduction_28 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut31 happy_x_2 of { happy_var_2 -> 
	happyIn17
		 (AbsLatte.Ret happy_var_2
	)}

happyReduce_29 = happySpecReduce_2  13# happyReduction_29
happyReduction_29 happy_x_2
	happy_x_1
	 =  happyIn17
		 (AbsLatte.VRet
	)

happyReduce_30 = happyReduce 5# 13# happyReduction_30
happyReduction_30 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut31 happy_x_3 of { happy_var_3 -> 
	case happyOut17 happy_x_5 of { happy_var_5 -> 
	happyIn17
		 (AbsLatte.Cond happy_var_3 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_31 = happyReduce 7# 13# happyReduction_31
happyReduction_31 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut31 happy_x_3 of { happy_var_3 -> 
	case happyOut17 happy_x_5 of { happy_var_5 -> 
	case happyOut17 happy_x_7 of { happy_var_7 -> 
	happyIn17
		 (AbsLatte.CondElse happy_var_3 happy_var_5 happy_var_7
	) `HappyStk` happyRest}}}

happyReduce_32 = happyReduce 5# 13# happyReduction_32
happyReduction_32 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut31 happy_x_3 of { happy_var_3 -> 
	case happyOut17 happy_x_5 of { happy_var_5 -> 
	happyIn17
		 (AbsLatte.While happy_var_3 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_33 = happySpecReduce_2  13# happyReduction_33
happyReduction_33 happy_x_2
	happy_x_1
	 =  case happyOut31 happy_x_1 of { happy_var_1 -> 
	happyIn17
		 (AbsLatte.SExp happy_var_1
	)}

happyReduce_34 = happyReduce 8# 13# happyReduction_34
happyReduction_34 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut20 happy_x_3 of { happy_var_3 -> 
	case happyOut4 happy_x_4 of { happy_var_4 -> 
	case happyOut31 happy_x_6 of { happy_var_6 -> 
	case happyOut17 happy_x_8 of { happy_var_8 -> 
	happyIn17
		 (AbsLatte.For happy_var_3 happy_var_4 happy_var_6 happy_var_8
	) `HappyStk` happyRest}}}}

happyReduce_35 = happySpecReduce_1  14# happyReduction_35
happyReduction_35 happy_x_1
	 =  case happyOut4 happy_x_1 of { happy_var_1 -> 
	happyIn18
		 (AbsLatte.NoInit happy_var_1
	)}

happyReduce_36 = happySpecReduce_3  14# happyReduction_36
happyReduction_36 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut4 happy_x_1 of { happy_var_1 -> 
	case happyOut31 happy_x_3 of { happy_var_3 -> 
	happyIn18
		 (AbsLatte.Init happy_var_1 happy_var_3
	)}}

happyReduce_37 = happySpecReduce_1  15# happyReduction_37
happyReduction_37 happy_x_1
	 =  case happyOut18 happy_x_1 of { happy_var_1 -> 
	happyIn19
		 ((:[]) happy_var_1
	)}

happyReduce_38 = happySpecReduce_3  15# happyReduction_38
happyReduction_38 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { happy_var_1 -> 
	case happyOut19 happy_x_3 of { happy_var_3 -> 
	happyIn19
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_39 = happySpecReduce_2  16# happyReduction_39
happyReduction_39 happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	happyIn20
		 (AbsLatte.Arr happy_var_1
	)}

happyReduce_40 = happySpecReduce_1  16# happyReduction_40
happyReduction_40 happy_x_1
	 =  case happyOut4 happy_x_1 of { happy_var_1 -> 
	happyIn20
		 (AbsLatte.Cls happy_var_1
	)}

happyReduce_41 = happySpecReduce_1  16# happyReduction_41
happyReduction_41 happy_x_1
	 =  happyIn20
		 (AbsLatte.Int
	)

happyReduce_42 = happySpecReduce_1  16# happyReduction_42
happyReduction_42 happy_x_1
	 =  happyIn20
		 (AbsLatte.Str
	)

happyReduce_43 = happySpecReduce_1  16# happyReduction_43
happyReduction_43 happy_x_1
	 =  happyIn20
		 (AbsLatte.Bool
	)

happyReduce_44 = happySpecReduce_1  16# happyReduction_44
happyReduction_44 happy_x_1
	 =  happyIn20
		 (AbsLatte.Void
	)

happyReduce_45 = happySpecReduce_0  17# happyReduction_45
happyReduction_45  =  happyIn21
		 ([]
	)

happyReduce_46 = happySpecReduce_1  17# happyReduction_46
happyReduction_46 happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	happyIn21
		 ((:[]) happy_var_1
	)}

happyReduce_47 = happySpecReduce_3  17# happyReduction_47
happyReduction_47 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	case happyOut21 happy_x_3 of { happy_var_3 -> 
	happyIn21
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_48 = happySpecReduce_1  18# happyReduction_48
happyReduction_48 happy_x_1
	 =  case happyOut4 happy_x_1 of { happy_var_1 -> 
	happyIn22
		 (AbsLatte.EVar happy_var_1
	)}

happyReduce_49 = happySpecReduce_3  18# happyReduction_49
happyReduction_49 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut23 happy_x_1 of { happy_var_1 -> 
	case happyOut4 happy_x_3 of { happy_var_3 -> 
	happyIn22
		 (AbsLatte.EAttrAcc happy_var_1 happy_var_3
	)}}

happyReduce_50 = happyReduce 4# 18# happyReduction_50
happyReduction_50 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut23 happy_x_1 of { happy_var_1 -> 
	case happyOut31 happy_x_3 of { happy_var_3 -> 
	happyIn22
		 (AbsLatte.EArrAcc happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_51 = happySpecReduce_3  18# happyReduction_51
happyReduction_51 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut31 happy_x_2 of { happy_var_2 -> 
	happyIn22
		 (happy_var_2
	)}

happyReduce_52 = happyReduce 6# 19# happyReduction_52
happyReduction_52 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut23 happy_x_1 of { happy_var_1 -> 
	case happyOut4 happy_x_3 of { happy_var_3 -> 
	case happyOut32 happy_x_5 of { happy_var_5 -> 
	happyIn23
		 (AbsLatte.EMethCall happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest}}}

happyReduce_53 = happyReduce 4# 19# happyReduction_53
happyReduction_53 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut4 happy_x_1 of { happy_var_1 -> 
	case happyOut32 happy_x_3 of { happy_var_3 -> 
	happyIn23
		 (AbsLatte.EApp happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_54 = happySpecReduce_3  19# happyReduction_54
happyReduction_54 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_2 of { happy_var_2 -> 
	case happyOut24 happy_x_3 of { happy_var_3 -> 
	happyIn23
		 (AbsLatte.ENew happy_var_2 happy_var_3
	)}}

happyReduce_55 = happySpecReduce_1  19# happyReduction_55
happyReduction_55 happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	happyIn23
		 (happy_var_1
	)}

happyReduce_56 = happySpecReduce_3  20# happyReduction_56
happyReduction_56 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut31 happy_x_2 of { happy_var_2 -> 
	happyIn24
		 (AbsLatte.ArrSize happy_var_2
	)}

happyReduce_57 = happySpecReduce_0  20# happyReduction_57
happyReduction_57  =  happyIn24
		 (AbsLatte.ClsNotArr
	)

happyReduce_58 = happySpecReduce_3  21# happyReduction_58
happyReduction_58 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_2 of { happy_var_2 -> 
	happyIn25
		 (AbsLatte.ECastNull happy_var_2
	)}

happyReduce_59 = happySpecReduce_1  21# happyReduction_59
happyReduction_59 happy_x_1
	 =  case happyOut5 happy_x_1 of { happy_var_1 -> 
	happyIn25
		 (AbsLatte.ELitInt happy_var_1
	)}

happyReduce_60 = happySpecReduce_1  21# happyReduction_60
happyReduction_60 happy_x_1
	 =  happyIn25
		 (AbsLatte.ELitTrue
	)

happyReduce_61 = happySpecReduce_1  21# happyReduction_61
happyReduction_61 happy_x_1
	 =  happyIn25
		 (AbsLatte.ELitFalse
	)

happyReduce_62 = happySpecReduce_1  21# happyReduction_62
happyReduction_62 happy_x_1
	 =  case happyOut6 happy_x_1 of { happy_var_1 -> 
	happyIn25
		 (AbsLatte.EString happy_var_1
	)}

happyReduce_63 = happySpecReduce_1  21# happyReduction_63
happyReduction_63 happy_x_1
	 =  case happyOut23 happy_x_1 of { happy_var_1 -> 
	happyIn25
		 (happy_var_1
	)}

happyReduce_64 = happySpecReduce_2  22# happyReduction_64
happyReduction_64 happy_x_2
	happy_x_1
	 =  case happyOut25 happy_x_2 of { happy_var_2 -> 
	happyIn26
		 (AbsLatte.Neg happy_var_2
	)}

happyReduce_65 = happySpecReduce_2  22# happyReduction_65
happyReduction_65 happy_x_2
	happy_x_1
	 =  case happyOut25 happy_x_2 of { happy_var_2 -> 
	happyIn26
		 (AbsLatte.Not happy_var_2
	)}

happyReduce_66 = happySpecReduce_1  22# happyReduction_66
happyReduction_66 happy_x_1
	 =  case happyOut25 happy_x_1 of { happy_var_1 -> 
	happyIn26
		 (happy_var_1
	)}

happyReduce_67 = happySpecReduce_3  23# happyReduction_67
happyReduction_67 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut27 happy_x_1 of { happy_var_1 -> 
	case happyOut34 happy_x_2 of { happy_var_2 -> 
	case happyOut26 happy_x_3 of { happy_var_3 -> 
	happyIn27
		 (AbsLatte.EMul happy_var_1 happy_var_2 happy_var_3
	)}}}

happyReduce_68 = happySpecReduce_1  23# happyReduction_68
happyReduction_68 happy_x_1
	 =  case happyOut26 happy_x_1 of { happy_var_1 -> 
	happyIn27
		 (happy_var_1
	)}

happyReduce_69 = happySpecReduce_3  24# happyReduction_69
happyReduction_69 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut33 happy_x_2 of { happy_var_2 -> 
	case happyOut27 happy_x_3 of { happy_var_3 -> 
	happyIn28
		 (AbsLatte.EAdd happy_var_1 happy_var_2 happy_var_3
	)}}}

happyReduce_70 = happySpecReduce_1  24# happyReduction_70
happyReduction_70 happy_x_1
	 =  case happyOut27 happy_x_1 of { happy_var_1 -> 
	happyIn28
		 (happy_var_1
	)}

happyReduce_71 = happySpecReduce_3  25# happyReduction_71
happyReduction_71 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	case happyOut35 happy_x_2 of { happy_var_2 -> 
	case happyOut28 happy_x_3 of { happy_var_3 -> 
	happyIn29
		 (AbsLatte.ERel happy_var_1 happy_var_2 happy_var_3
	)}}}

happyReduce_72 = happySpecReduce_1  25# happyReduction_72
happyReduction_72 happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	happyIn29
		 (happy_var_1
	)}

happyReduce_73 = happySpecReduce_3  26# happyReduction_73
happyReduction_73 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	case happyOut30 happy_x_3 of { happy_var_3 -> 
	happyIn30
		 (AbsLatte.EAnd happy_var_1 happy_var_3
	)}}

happyReduce_74 = happySpecReduce_1  26# happyReduction_74
happyReduction_74 happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	happyIn30
		 (happy_var_1
	)}

happyReduce_75 = happySpecReduce_3  27# happyReduction_75
happyReduction_75 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut30 happy_x_1 of { happy_var_1 -> 
	case happyOut31 happy_x_3 of { happy_var_3 -> 
	happyIn31
		 (AbsLatte.EOr happy_var_1 happy_var_3
	)}}

happyReduce_76 = happySpecReduce_1  27# happyReduction_76
happyReduction_76 happy_x_1
	 =  case happyOut30 happy_x_1 of { happy_var_1 -> 
	happyIn31
		 (happy_var_1
	)}

happyReduce_77 = happySpecReduce_0  28# happyReduction_77
happyReduction_77  =  happyIn32
		 ([]
	)

happyReduce_78 = happySpecReduce_1  28# happyReduction_78
happyReduction_78 happy_x_1
	 =  case happyOut31 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 ((:[]) happy_var_1
	)}

happyReduce_79 = happySpecReduce_3  28# happyReduction_79
happyReduction_79 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut31 happy_x_1 of { happy_var_1 -> 
	case happyOut32 happy_x_3 of { happy_var_3 -> 
	happyIn32
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_80 = happySpecReduce_1  29# happyReduction_80
happyReduction_80 happy_x_1
	 =  happyIn33
		 (AbsLatte.Plus
	)

happyReduce_81 = happySpecReduce_1  29# happyReduction_81
happyReduction_81 happy_x_1
	 =  happyIn33
		 (AbsLatte.Minus
	)

happyReduce_82 = happySpecReduce_1  30# happyReduction_82
happyReduction_82 happy_x_1
	 =  happyIn34
		 (AbsLatte.Times
	)

happyReduce_83 = happySpecReduce_1  30# happyReduction_83
happyReduction_83 happy_x_1
	 =  happyIn34
		 (AbsLatte.Div
	)

happyReduce_84 = happySpecReduce_1  30# happyReduction_84
happyReduction_84 happy_x_1
	 =  happyIn34
		 (AbsLatte.Mod
	)

happyReduce_85 = happySpecReduce_1  31# happyReduction_85
happyReduction_85 happy_x_1
	 =  happyIn35
		 (AbsLatte.LTH
	)

happyReduce_86 = happySpecReduce_1  31# happyReduction_86
happyReduction_86 happy_x_1
	 =  happyIn35
		 (AbsLatte.LE
	)

happyReduce_87 = happySpecReduce_1  31# happyReduction_87
happyReduction_87 happy_x_1
	 =  happyIn35
		 (AbsLatte.GTH
	)

happyReduce_88 = happySpecReduce_1  31# happyReduction_88
happyReduction_88 happy_x_1
	 =  happyIn35
		 (AbsLatte.GE
	)

happyReduce_89 = happySpecReduce_1  31# happyReduction_89
happyReduction_89 happy_x_1
	 =  happyIn35
		 (AbsLatte.EQU
	)

happyReduce_90 = happySpecReduce_1  31# happyReduction_90
happyReduction_90 happy_x_1
	 =  happyIn35
		 (AbsLatte.NE
	)

happyNewToken action sts stk [] =
	happyDoAction 47# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 1#;
	PT _ (TS _ 2) -> cont 2#;
	PT _ (TS _ 3) -> cont 3#;
	PT _ (TS _ 4) -> cont 4#;
	PT _ (TS _ 5) -> cont 5#;
	PT _ (TS _ 6) -> cont 6#;
	PT _ (TS _ 7) -> cont 7#;
	PT _ (TS _ 8) -> cont 8#;
	PT _ (TS _ 9) -> cont 9#;
	PT _ (TS _ 10) -> cont 10#;
	PT _ (TS _ 11) -> cont 11#;
	PT _ (TS _ 12) -> cont 12#;
	PT _ (TS _ 13) -> cont 13#;
	PT _ (TS _ 14) -> cont 14#;
	PT _ (TS _ 15) -> cont 15#;
	PT _ (TS _ 16) -> cont 16#;
	PT _ (TS _ 17) -> cont 17#;
	PT _ (TS _ 18) -> cont 18#;
	PT _ (TS _ 19) -> cont 19#;
	PT _ (TS _ 20) -> cont 20#;
	PT _ (TS _ 21) -> cont 21#;
	PT _ (TS _ 22) -> cont 22#;
	PT _ (TS _ 23) -> cont 23#;
	PT _ (TS _ 24) -> cont 24#;
	PT _ (TS _ 25) -> cont 25#;
	PT _ (TS _ 26) -> cont 26#;
	PT _ (TS _ 27) -> cont 27#;
	PT _ (TS _ 28) -> cont 28#;
	PT _ (TS _ 29) -> cont 29#;
	PT _ (TS _ 30) -> cont 30#;
	PT _ (TS _ 31) -> cont 31#;
	PT _ (TS _ 32) -> cont 32#;
	PT _ (TS _ 33) -> cont 33#;
	PT _ (TS _ 34) -> cont 34#;
	PT _ (TS _ 35) -> cont 35#;
	PT _ (TS _ 36) -> cont 36#;
	PT _ (TS _ 37) -> cont 37#;
	PT _ (TS _ 38) -> cont 38#;
	PT _ (TS _ 39) -> cont 39#;
	PT _ (TS _ 40) -> cont 40#;
	PT _ (TS _ 41) -> cont 41#;
	PT _ (TS _ 42) -> cont 42#;
	PT _ (TS _ 43) -> cont 43#;
	PT _ (TV happy_dollar_dollar) -> cont 44#;
	PT _ (TI happy_dollar_dollar) -> cont 45#;
	PT _ (TL happy_dollar_dollar) -> cont 46#;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 47# tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = (thenM)
happyReturn :: () => a -> Err a
happyReturn = (returnM)
happyThen1 m k tks = (thenM) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (returnM) a
happyError' :: () => ([(Token)], [String]) -> Err a
happyError' = (\(tokens, _) -> happyError tokens)
pProgram tks = happySomeParser where
 happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (happyOut7 x))

happySeq = happyDontSeq


returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    t:_ -> " before `" ++ id(prToken t) ++ "'"

myLexer = tokens
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 11 "<command-line>" #-}
# 1 "/usr/include/stdc-predef.h" 1 3 4

# 17 "/usr/include/stdc-predef.h" 3 4














































{-# LINE 11 "<command-line>" #-}
{-# LINE 1 "/usr/lib/ghc/include/ghcversion.h" #-}

















{-# LINE 11 "<command-line>" #-}
{-# LINE 1 "/tmp/ghcb5f8_0/ghc_2.h" #-}




























































































































































{-# LINE 11 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 













-- Do not remove this comment. Required to fix CPP parsing when using GCC and a clang-compiled alex.
#if __GLASGOW_HASKELL__ > 706
#define LT(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.<# m)) :: Bool)
#define GTE(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.>=# m)) :: Bool)
#define EQ(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.==# m)) :: Bool)
#else
#define LT(n,m) (n Happy_GHC_Exts.<# m)
#define GTE(n,m) (n Happy_GHC_Exts.>=# m)
#define EQ(n,m) (n Happy_GHC_Exts.==# m)
#endif
{-# LINE 43 "templates/GenericTemplate.hs" #-}

data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList







{-# LINE 65 "templates/GenericTemplate.hs" #-}

{-# LINE 75 "templates/GenericTemplate.hs" #-}

{-# LINE 84 "templates/GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is 0#, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
        (happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
        = {- nothing -}


          case action of
                0#           -> {- nothing -}
                                     happyFail (happyExpListPerState ((Happy_GHC_Exts.I# (st)) :: Int)) i tk st
                -1#          -> {- nothing -}
                                     happyAccept i tk st
                n | LT(n,(0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}

                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
                n                 -> {- nothing -}


                                     happyShift new_state i tk st
                                     where new_state = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where off    = happyAdjustOffset (indexShortOffAddr happyActOffsets st)
         off_i  = (off Happy_GHC_Exts.+#  i)
         check  = if GTE(off_i,(0# :: Happy_GHC_Exts.Int#))
                  then EQ(indexShortOffAddr happyCheck off_i, i)
                  else False
         action
          | check     = indexShortOffAddr happyTable off_i
          | otherwise = indexShortOffAddr happyDefActions st




indexShortOffAddr (HappyA# arr) off =
        Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#




{-# INLINE happyLt #-}
happyLt x y = LT(x,y)


readArrayBit arr bit =
    Bits.testBit (Happy_GHC_Exts.I# (indexShortOffAddr arr ((unbox_int bit) `Happy_GHC_Exts.iShiftRA#` 4#))) (bit `mod` 16)
  where unbox_int (Happy_GHC_Exts.I# x) = x






data HappyAddr = HappyA# Happy_GHC_Exts.Addr#


-----------------------------------------------------------------------------
-- HappyState data type (not arrays)

{-# LINE 180 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) sts of
         sts1@((HappyCons (st1@(action)) (_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
         let drop_stk = happyDropStk k stk

             off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st1)
             off_i = (off Happy_GHC_Exts.+#  nt)
             new_state = indexShortOffAddr happyTable off_i




          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st)
         off_i = (off Happy_GHC_Exts.+#  nt)
         new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (0# is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist 0# tk old_st _ stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  0# tk old_st (HappyCons ((action)) (sts)) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        happyDoAction 0# tk action sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (action) sts stk =
--      trace "entering error recovery" $
        happyDoAction 0# tk action sts ( (Happy_GHC_Exts.unsafeCoerce# (Happy_GHC_Exts.I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
