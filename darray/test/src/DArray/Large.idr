-- This tests compiler performance when processing a huge
-- enum type
module DArray.Large

import DArray.Util
import Data.DArray
import Data.Finite
import Derive.Finite
import Derive.HDecEq
import Derive.Prelude

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
  V101 : MyTyp
  V102 : MyTyp
  V103 : MyTyp
  V104 : MyTyp
  V105 : MyTyp
  V106 : MyTyp
  V107 : MyTyp
  V108 : MyTyp
  V109 : MyTyp
  V110 : MyTyp
  V111 : MyTyp
  V112 : MyTyp
  V113 : MyTyp
  V114 : MyTyp
  V115 : MyTyp
  V116 : MyTyp
  V117 : MyTyp
  V118 : MyTyp
  V119 : MyTyp
  V120 : MyTyp
  V121 : MyTyp
  V122 : MyTyp
  V123 : MyTyp
  V124 : MyTyp
  V125 : MyTyp
  V126 : MyTyp
  V127 : MyTyp
  V128 : MyTyp
  V129 : MyTyp
  V130 : MyTyp
  V131 : MyTyp
  V132 : MyTyp
  V133 : MyTyp
  V134 : MyTyp
  V135 : MyTyp
  V136 : MyTyp
  V137 : MyTyp
  V138 : MyTyp
  V139 : MyTyp
  V140 : MyTyp
  V141 : MyTyp
  V142 : MyTyp
  V143 : MyTyp
  V144 : MyTyp
  V145 : MyTyp
  V146 : MyTyp
  V147 : MyTyp
  V148 : MyTyp
  V149 : MyTyp
  V150 : MyTyp
  V151 : MyTyp
  V152 : MyTyp
  V153 : MyTyp
  V154 : MyTyp
  V155 : MyTyp
  V156 : MyTyp
  V157 : MyTyp
  V158 : MyTyp
  V159 : MyTyp
  V160 : MyTyp
  V161 : MyTyp
  V162 : MyTyp
  V163 : MyTyp
  V164 : MyTyp
  V165 : MyTyp
  V166 : MyTyp
  V167 : MyTyp
  V168 : MyTyp
  V169 : MyTyp
  V170 : MyTyp
  V171 : MyTyp
  V172 : MyTyp
  V173 : MyTyp
  V174 : MyTyp
  V175 : MyTyp
  V176 : MyTyp
  V177 : MyTyp
  V178 : MyTyp
  V179 : MyTyp
  V180 : MyTyp
  V181 : MyTyp
  V182 : MyTyp
  V183 : MyTyp
  V184 : MyTyp
  V185 : MyTyp
  V186 : MyTyp
  V187 : MyTyp
  V188 : MyTyp
  V189 : MyTyp
  V190 : MyTyp
  V191 : MyTyp
  V192 : MyTyp
  V193 : MyTyp
  V194 : MyTyp
  V195 : MyTyp
  V196 : MyTyp
  V197 : MyTyp
  V198 : MyTyp
  V199 : MyTyp
  V200 : MyTyp
  V201 : MyTyp
  V202 : MyTyp
  V203 : MyTyp
  V204 : MyTyp
  V205 : MyTyp
  V206 : MyTyp
  V207 : MyTyp
  V208 : MyTyp
  V209 : MyTyp
  V210 : MyTyp
  V211 : MyTyp
  V212 : MyTyp
  V213 : MyTyp
  V214 : MyTyp
  V215 : MyTyp
  V216 : MyTyp
  V217 : MyTyp
  V218 : MyTyp
  V219 : MyTyp
  V220 : MyTyp
  V221 : MyTyp
  V222 : MyTyp
  V223 : MyTyp
  V224 : MyTyp
  V225 : MyTyp
  V226 : MyTyp
  V227 : MyTyp
  V228 : MyTyp
  V229 : MyTyp
  V230 : MyTyp
  V231 : MyTyp
  V232 : MyTyp
  V233 : MyTyp
  V234 : MyTyp
  V235 : MyTyp
  V236 : MyTyp
  V237 : MyTyp
  V238 : MyTyp
  V239 : MyTyp
  V240 : MyTyp
  V241 : MyTyp
  V242 : MyTyp
  V243 : MyTyp
  V244 : MyTyp
  V245 : MyTyp
  V246 : MyTyp
  V247 : MyTyp
  V248 : MyTyp
  V249 : MyTyp
  V250 : MyTyp
  V251 : MyTyp
  V252 : MyTyp
  V253 : MyTyp
  V254 : MyTyp
  V255 : MyTyp

%runElab derive "MyTyp" [Show,Eq,Ord,Finite,HDecEq]

public export
0 Typ : MyTyp -> Type
Typ _ = String

export
0 allInValues : (v : MyTyp) -> inList v Finite.values === True

export
0 allLT : (v : MyTyp) -> lt (cast $ conIndexMyTyp v) 255 === True

export %inline
Enum MyTyp 255 where
  toFin x = natToFinLT (cast $ conIndexMyTyp x) @{ltReflectsLT _ _ $ allLT x}

test : DArray MyTyp Typ
test = darray _ _ values (\v => hdecEqInList v (allInValues v)) (\_ => "foo")

allInValues V1 = Refl
allInValues V2 = Refl
allInValues V3 = Refl
allInValues V4 = Refl
allInValues V5 = Refl
allInValues V6 = Refl
allInValues V7 = Refl
allInValues V8 = Refl
allInValues V9 = Refl
allInValues V10 = Refl
allInValues V11 = Refl
allInValues V12 = Refl
allInValues V13 = Refl
allInValues V14 = Refl
allInValues V15 = Refl
allInValues V16 = Refl
allInValues V17 = Refl
allInValues V18 = Refl
allInValues V19 = Refl
allInValues V20 = Refl
allInValues V21 = Refl
allInValues V22 = Refl
allInValues V23 = Refl
allInValues V24 = Refl
allInValues V25 = Refl
allInValues V26 = Refl
allInValues V27 = Refl
allInValues V28 = Refl
allInValues V29 = Refl
allInValues V30 = Refl
allInValues V31 = Refl
allInValues V32 = Refl
allInValues V33 = Refl
allInValues V34 = Refl
allInValues V35 = Refl
allInValues V36 = Refl
allInValues V37 = Refl
allInValues V38 = Refl
allInValues V39 = Refl
allInValues V40 = Refl
allInValues V41 = Refl
allInValues V42 = Refl
allInValues V43 = Refl
allInValues V44 = Refl
allInValues V45 = Refl
allInValues V46 = Refl
allInValues V47 = Refl
allInValues V48 = Refl
allInValues V49 = Refl
allInValues V50 = Refl
allInValues V51 = Refl
allInValues V52 = Refl
allInValues V53 = Refl
allInValues V54 = Refl
allInValues V55 = Refl
allInValues V56 = Refl
allInValues V57 = Refl
allInValues V58 = Refl
allInValues V59 = Refl
allInValues V60 = Refl
allInValues V61 = Refl
allInValues V62 = Refl
allInValues V63 = Refl
allInValues V64 = Refl
allInValues V65 = Refl
allInValues V66 = Refl
allInValues V67 = Refl
allInValues V68 = Refl
allInValues V69 = Refl
allInValues V70 = Refl
allInValues V71 = Refl
allInValues V72 = Refl
allInValues V73 = Refl
allInValues V74 = Refl
allInValues V75 = Refl
allInValues V76 = Refl
allInValues V77 = Refl
allInValues V78 = Refl
allInValues V79 = Refl
allInValues V80 = Refl
allInValues V81 = Refl
allInValues V82 = Refl
allInValues V83 = Refl
allInValues V84 = Refl
allInValues V85 = Refl
allInValues V86 = Refl
allInValues V87 = Refl
allInValues V88 = Refl
allInValues V89 = Refl
allInValues V90 = Refl
allInValues V91 = Refl
allInValues V92 = Refl
allInValues V93 = Refl
allInValues V94 = Refl
allInValues V95 = Refl
allInValues V96 = Refl
allInValues V97 = Refl
allInValues V98 = Refl
allInValues V99 = Refl
allInValues V100 = Refl
allInValues V101 = Refl
allInValues V102 = Refl
allInValues V103 = Refl
allInValues V104 = Refl
allInValues V105 = Refl
allInValues V106 = Refl
allInValues V107 = Refl
allInValues V108 = Refl
allInValues V109 = Refl
allInValues V110 = Refl
allInValues V111 = Refl
allInValues V112 = Refl
allInValues V113 = Refl
allInValues V114 = Refl
allInValues V115 = Refl
allInValues V116 = Refl
allInValues V117 = Refl
allInValues V118 = Refl
allInValues V119 = Refl
allInValues V120 = Refl
allInValues V121 = Refl
allInValues V122 = Refl
allInValues V123 = Refl
allInValues V124 = Refl
allInValues V125 = Refl
allInValues V126 = Refl
allInValues V127 = Refl
allInValues V128 = Refl
allInValues V129 = Refl
allInValues V130 = Refl
allInValues V131 = Refl
allInValues V132 = Refl
allInValues V133 = Refl
allInValues V134 = Refl
allInValues V135 = Refl
allInValues V136 = Refl
allInValues V137 = Refl
allInValues V138 = Refl
allInValues V139 = Refl
allInValues V140 = Refl
allInValues V141 = Refl
allInValues V142 = Refl
allInValues V143 = Refl
allInValues V144 = Refl
allInValues V145 = Refl
allInValues V146 = Refl
allInValues V147 = Refl
allInValues V148 = Refl
allInValues V149 = Refl
allInValues V150 = Refl
allInValues V151 = Refl
allInValues V152 = Refl
allInValues V153 = Refl
allInValues V154 = Refl
allInValues V155 = Refl
allInValues V156 = Refl
allInValues V157 = Refl
allInValues V158 = Refl
allInValues V159 = Refl
allInValues V160 = Refl
allInValues V161 = Refl
allInValues V162 = Refl
allInValues V163 = Refl
allInValues V164 = Refl
allInValues V165 = Refl
allInValues V166 = Refl
allInValues V167 = Refl
allInValues V168 = Refl
allInValues V169 = Refl
allInValues V170 = Refl
allInValues V171 = Refl
allInValues V172 = Refl
allInValues V173 = Refl
allInValues V174 = Refl
allInValues V175 = Refl
allInValues V176 = Refl
allInValues V177 = Refl
allInValues V178 = Refl
allInValues V179 = Refl
allInValues V180 = Refl
allInValues V181 = Refl
allInValues V182 = Refl
allInValues V183 = Refl
allInValues V184 = Refl
allInValues V185 = Refl
allInValues V186 = Refl
allInValues V187 = Refl
allInValues V188 = Refl
allInValues V189 = Refl
allInValues V190 = Refl
allInValues V191 = Refl
allInValues V192 = Refl
allInValues V193 = Refl
allInValues V194 = Refl
allInValues V195 = Refl
allInValues V196 = Refl
allInValues V197 = Refl
allInValues V198 = Refl
allInValues V199 = Refl
allInValues V200 = Refl
allInValues V201 = Refl
allInValues V202 = Refl
allInValues V203 = Refl
allInValues V204 = Refl
allInValues V205 = Refl
allInValues V206 = Refl
allInValues V207 = Refl
allInValues V208 = Refl
allInValues V209 = Refl
allInValues V210 = Refl
allInValues V211 = Refl
allInValues V212 = Refl
allInValues V213 = Refl
allInValues V214 = Refl
allInValues V215 = Refl
allInValues V216 = Refl
allInValues V217 = Refl
allInValues V218 = Refl
allInValues V219 = Refl
allInValues V220 = Refl
allInValues V221 = Refl
allInValues V222 = Refl
allInValues V223 = Refl
allInValues V224 = Refl
allInValues V225 = Refl
allInValues V226 = Refl
allInValues V227 = Refl
allInValues V228 = Refl
allInValues V229 = Refl
allInValues V230 = Refl
allInValues V231 = Refl
allInValues V232 = Refl
allInValues V233 = Refl
allInValues V234 = Refl
allInValues V235 = Refl
allInValues V236 = Refl
allInValues V237 = Refl
allInValues V238 = Refl
allInValues V239 = Refl
allInValues V240 = Refl
allInValues V241 = Refl
allInValues V242 = Refl
allInValues V243 = Refl
allInValues V244 = Refl
allInValues V245 = Refl
allInValues V246 = Refl
allInValues V247 = Refl
allInValues V248 = Refl
allInValues V249 = Refl
allInValues V250 = Refl
allInValues V251 = Refl
allInValues V252 = Refl
allInValues V253 = Refl
allInValues V254 = Refl
allInValues V255 = Refl

allLT V1 = Refl
allLT V2 = Refl
allLT V3 = Refl
allLT V4 = Refl
allLT V5 = Refl
allLT V6 = Refl
allLT V7 = Refl
allLT V8 = Refl
allLT V9 = Refl
allLT V10 = Refl
allLT V11 = Refl
allLT V12 = Refl
allLT V13 = Refl
allLT V14 = Refl
allLT V15 = Refl
allLT V16 = Refl
allLT V17 = Refl
allLT V18 = Refl
allLT V19 = Refl
allLT V20 = Refl
allLT V21 = Refl
allLT V22 = Refl
allLT V23 = Refl
allLT V24 = Refl
allLT V25 = Refl
allLT V26 = Refl
allLT V27 = Refl
allLT V28 = Refl
allLT V29 = Refl
allLT V30 = Refl
allLT V31 = Refl
allLT V32 = Refl
allLT V33 = Refl
allLT V34 = Refl
allLT V35 = Refl
allLT V36 = Refl
allLT V37 = Refl
allLT V38 = Refl
allLT V39 = Refl
allLT V40 = Refl
allLT V41 = Refl
allLT V42 = Refl
allLT V43 = Refl
allLT V44 = Refl
allLT V45 = Refl
allLT V46 = Refl
allLT V47 = Refl
allLT V48 = Refl
allLT V49 = Refl
allLT V50 = Refl
allLT V51 = Refl
allLT V52 = Refl
allLT V53 = Refl
allLT V54 = Refl
allLT V55 = Refl
allLT V56 = Refl
allLT V57 = Refl
allLT V58 = Refl
allLT V59 = Refl
allLT V60 = Refl
allLT V61 = Refl
allLT V62 = Refl
allLT V63 = Refl
allLT V64 = Refl
allLT V65 = Refl
allLT V66 = Refl
allLT V67 = Refl
allLT V68 = Refl
allLT V69 = Refl
allLT V70 = Refl
allLT V71 = Refl
allLT V72 = Refl
allLT V73 = Refl
allLT V74 = Refl
allLT V75 = Refl
allLT V76 = Refl
allLT V77 = Refl
allLT V78 = Refl
allLT V79 = Refl
allLT V80 = Refl
allLT V81 = Refl
allLT V82 = Refl
allLT V83 = Refl
allLT V84 = Refl
allLT V85 = Refl
allLT V86 = Refl
allLT V87 = Refl
allLT V88 = Refl
allLT V89 = Refl
allLT V90 = Refl
allLT V91 = Refl
allLT V92 = Refl
allLT V93 = Refl
allLT V94 = Refl
allLT V95 = Refl
allLT V96 = Refl
allLT V97 = Refl
allLT V98 = Refl
allLT V99 = Refl
allLT V100 = Refl
allLT V101 = Refl
allLT V102 = Refl
allLT V103 = Refl
allLT V104 = Refl
allLT V105 = Refl
allLT V106 = Refl
allLT V107 = Refl
allLT V108 = Refl
allLT V109 = Refl
allLT V110 = Refl
allLT V111 = Refl
allLT V112 = Refl
allLT V113 = Refl
allLT V114 = Refl
allLT V115 = Refl
allLT V116 = Refl
allLT V117 = Refl
allLT V118 = Refl
allLT V119 = Refl
allLT V120 = Refl
allLT V121 = Refl
allLT V122 = Refl
allLT V123 = Refl
allLT V124 = Refl
allLT V125 = Refl
allLT V126 = Refl
allLT V127 = Refl
allLT V128 = Refl
allLT V129 = Refl
allLT V130 = Refl
allLT V131 = Refl
allLT V132 = Refl
allLT V133 = Refl
allLT V134 = Refl
allLT V135 = Refl
allLT V136 = Refl
allLT V137 = Refl
allLT V138 = Refl
allLT V139 = Refl
allLT V140 = Refl
allLT V141 = Refl
allLT V142 = Refl
allLT V143 = Refl
allLT V144 = Refl
allLT V145 = Refl
allLT V146 = Refl
allLT V147 = Refl
allLT V148 = Refl
allLT V149 = Refl
allLT V150 = Refl
allLT V151 = Refl
allLT V152 = Refl
allLT V153 = Refl
allLT V154 = Refl
allLT V155 = Refl
allLT V156 = Refl
allLT V157 = Refl
allLT V158 = Refl
allLT V159 = Refl
allLT V160 = Refl
allLT V161 = Refl
allLT V162 = Refl
allLT V163 = Refl
allLT V164 = Refl
allLT V165 = Refl
allLT V166 = Refl
allLT V167 = Refl
allLT V168 = Refl
allLT V169 = Refl
allLT V170 = Refl
allLT V171 = Refl
allLT V172 = Refl
allLT V173 = Refl
allLT V174 = Refl
allLT V175 = Refl
allLT V176 = Refl
allLT V177 = Refl
allLT V178 = Refl
allLT V179 = Refl
allLT V180 = Refl
allLT V181 = Refl
allLT V182 = Refl
allLT V183 = Refl
allLT V184 = Refl
allLT V185 = Refl
allLT V186 = Refl
allLT V187 = Refl
allLT V188 = Refl
allLT V189 = Refl
allLT V190 = Refl
allLT V191 = Refl
allLT V192 = Refl
allLT V193 = Refl
allLT V194 = Refl
allLT V195 = Refl
allLT V196 = Refl
allLT V197 = Refl
allLT V198 = Refl
allLT V199 = Refl
allLT V200 = Refl
allLT V201 = Refl
allLT V202 = Refl
allLT V203 = Refl
allLT V204 = Refl
allLT V205 = Refl
allLT V206 = Refl
allLT V207 = Refl
allLT V208 = Refl
allLT V209 = Refl
allLT V210 = Refl
allLT V211 = Refl
allLT V212 = Refl
allLT V213 = Refl
allLT V214 = Refl
allLT V215 = Refl
allLT V216 = Refl
allLT V217 = Refl
allLT V218 = Refl
allLT V219 = Refl
allLT V220 = Refl
allLT V221 = Refl
allLT V222 = Refl
allLT V223 = Refl
allLT V224 = Refl
allLT V225 = Refl
allLT V226 = Refl
allLT V227 = Refl
allLT V228 = Refl
allLT V229 = Refl
allLT V230 = Refl
allLT V231 = Refl
allLT V232 = Refl
allLT V233 = Refl
allLT V234 = Refl
allLT V235 = Refl
allLT V236 = Refl
allLT V237 = Refl
allLT V238 = Refl
allLT V239 = Refl
allLT V240 = Refl
allLT V241 = Refl
allLT V242 = Refl
allLT V243 = Refl
allLT V244 = Refl
allLT V245 = Refl
allLT V246 = Refl
allLT V247 = Refl
allLT V248 = Refl
allLT V249 = Refl
allLT V250 = Refl
allLT V251 = Refl
allLT V252 = Refl
allLT V253 = Refl
allLT V254 = Refl
allLT V255 = Refl
