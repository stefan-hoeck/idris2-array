-- This tests compiler performance when processing a huge
-- enum type
module DArray.Large

import Data.DArray
import Derive.Enum
import Derive.HDecEq

%default total
%language ElabReflection

data MyTyp : Type where
  V1 : MyTyp
  V2 : MyTyp
  V3 : MyTyp
  V4 : MyTyp
  V5 : MyTyp
  V6 : MyTyp
  V7 : MyTyp
  V8 : MyTyp
  V9 : MyTyp
  V10 : MyTyp
  V11 : MyTyp
  V12 : MyTyp
  V13 : MyTyp
  V14 : MyTyp
  V15 : MyTyp
  V16 : MyTyp
  V17 : MyTyp
  V18 : MyTyp
  V19 : MyTyp
  V20 : MyTyp
  V21 : MyTyp
  V22 : MyTyp
  V23 : MyTyp
  V24 : MyTyp
  V25 : MyTyp
  V26 : MyTyp
  V27 : MyTyp
  V28 : MyTyp
  V29 : MyTyp
  V30 : MyTyp
  V31 : MyTyp
  V32 : MyTyp
  V33 : MyTyp
  V34 : MyTyp
  V35 : MyTyp
  V36 : MyTyp
  V37 : MyTyp
  V38 : MyTyp
  V39 : MyTyp
  V40 : MyTyp
  V41 : MyTyp
  V42 : MyTyp
  V43 : MyTyp
  V44 : MyTyp
  V45 : MyTyp
  V46 : MyTyp
  V47 : MyTyp
  V48 : MyTyp
  V49 : MyTyp
  V50 : MyTyp
  V51 : MyTyp
  V52 : MyTyp
  V53 : MyTyp
  V54 : MyTyp
  V55 : MyTyp
  V56 : MyTyp
  V57 : MyTyp
  V58 : MyTyp
  V59 : MyTyp
  V60 : MyTyp
  V61 : MyTyp
  V62 : MyTyp
  V63 : MyTyp
  V64 : MyTyp
  V65 : MyTyp
  V66 : MyTyp
  V67 : MyTyp
  V68 : MyTyp
  V69 : MyTyp
  V70 : MyTyp
  V71 : MyTyp
  V72 : MyTyp
  V73 : MyTyp
  V74 : MyTyp
  V75 : MyTyp
  V76 : MyTyp
  V77 : MyTyp
  V78 : MyTyp
  V79 : MyTyp
  V80 : MyTyp
  V81 : MyTyp
  V82 : MyTyp
  V83 : MyTyp
  V84 : MyTyp
  V85 : MyTyp
  V86 : MyTyp
  V87 : MyTyp
  V88 : MyTyp
  V89 : MyTyp
  V90 : MyTyp
  V91 : MyTyp
  V92 : MyTyp
  V93 : MyTyp
  V94 : MyTyp
  V95 : MyTyp
  V96 : MyTyp
  V97 : MyTyp
  V98 : MyTyp
  V99 : MyTyp
  V100 : MyTyp

%runElab derive "MyTyp" [Show,Enum,HDecEq]

public export
0 Typ : MyTyp -> Type
Typ _ = String

test : DArray MyTyp Typ
test = darray _ _ (\_ => "foo")
