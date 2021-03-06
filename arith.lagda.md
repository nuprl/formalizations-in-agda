```
module arith where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_ā”_; refl)
open Eq.ā”-Reasoning
open import Data.Nat using (ā)
open import Function using (_ā_)
import Data.Bool as š¹

-- open import Agda.Builtin.Sigma
open import Data.Product
```

The syntax of arithmetic expressions.

```
data term : Set where

  [_] :
      (n : ā)
      -------
    ā term

  tru : term

  fls : term

  _+_ :
     term ā term ā term

  _-_ :
     term ā term ā term

  if_then_else_ :
     term ā term ā term ā term

ex : term
ex = [ 3 ] + [ 4 ]

ex2 : term
ex2 = if tru then [ 3 ] else fls

data type : Set where

  Bool : type
  Nat : type

data ā¢'_ : type ā Set where
  [_]' :
      (n : ā)
      -------------
    ā ā¢' Nat

  tru' :
      ------------
      ā¢' Bool

  fls' :
      ------------
      ā¢' Bool

  _+'_ :
      ā¢' Nat
    ā ā¢' Nat
      --------------
    ā ā¢' Nat

  _-'_ :
      ā¢' Nat
    ā ā¢' Nat
      --------------
    ā ā¢' Nat

  if'_then_else_ : {Ļ : type}
    ā ā¢' Bool
    ā ā¢' Ļ
    ā ā¢' Ļ
      ---------------------------
    ā ā¢' Ļ


data ā¢_ā¶_ : term ā type ā Set where

  INat :
      (n : ā)
      -------------
    ā ā¢ [ n ] ā¶ Nat

  IBoolT :
      ------------
      ā¢ tru ā¶ Bool

  IBoolF :
      ------------
      ā¢ fls ā¶ Bool

  ENat+ :
      (eā eā : term)
    ā ā¢ eā ā¶ Nat
    ā ā¢ eā ā¶ Nat
      --------------
    ā ā¢ eā + eā ā¶ Nat

  ENat- :
      (eā eā : term)
    ā ā¢ eā ā¶ Nat
    ā ā¢ eā ā¶ Nat
      --------------
    ā ā¢ eā - eā ā¶ Nat

  IIf :
      (eā eā eā : term) (Ļ : type)
    ā ā¢ eā ā¶ Bool
    ā ā¢ eā ā¶ Ļ
    ā ā¢ eā ā¶ Ļ
      ---------------------------
    ā ā¢ if eā then eā else eā ā¶ Ļ

šÆā¦_ā§ : type ā Set
šÆā¦ Bool ā§ =  š¹.Bool
šÆā¦ Nat ā§ =  ā

ā¦_ā§ : {e : term} {Ļ : type} ā ā¢ e ā¶ Ļ ā šÆā¦ Ļ ā§
ā¦ INat n ā§ =  n
ā¦ IBoolT ā§ =  š¹.true
ā¦ IBoolF ā§ =  š¹.false
ā¦ ENat+ eā eā tj tjā ā§ = ā¦ tj ā§ Data.Nat.+ ā¦ tjā ā§
ā¦ ENat- eā eā tj tjā ā§ = ā¦ tj ā§ Data.Nat.āø ā¦ tjā ā§
ā¦ IIf eā eā eā _ tj tjā tjā ā§ = š¹.if ā¦ tj ā§ then ā¦ tjā ā§ else ā¦ tjā ā§

test : (e : term) (t : type) {{prf : ā¢ e ā¶ t}} -> ā¢ e ā¶ t
test e t {{prf}} = prf

test2 : ā¢' Nat
test2 = [ 0 ]' +' [ 1 ]'

interp : {Ļ : type} ā ā¢' Ļ ā šÆā¦ Ļ ā§
interp [ n ]' = n
interp tru' =  š¹.true
interp fls' =  š¹.false
interp (e +' eā) = interp e Data.Nat.+ interp eā
interp (e -' eā) = interp e Data.Nat.āø interp eā
interp (if' e then eā else eā) = š¹.if (interp e) then interp eā else interp eā
```

# Operational semantics of arith

```
infix 18 _ā¶_
data _ā¶_ : term ā term ā Set where

  ā¶+ : ā m n ā [ n ] + [ m ] ā¶ [ n Data.Nat.+ m ]
  ā¶- : ā m n ā [ n ] - [ m ] ā¶ [ n Data.Nat.āø m ]
  ā¶tru : ā {eā eā} ā if tru then eā else eā ā¶ eā
  ā¶fls : ā {eā eā} ā if fls then eā else eā ā¶ eā

  ā¶+l : ā eā eā' eā ā
       eā ā¶ eā'
       -----------------
    ā eā + eā ā¶ eā' + eā

  ā¶+r : ā eā eā' eā ā
       eā ā¶ eā'
       ---------------------
    ā eā + eā ā¶ eā + eā'

  ā¶-l : ā eā eā' eā ā eā ā¶ eā' ā eā - eā ā¶ eā' - eā
  ā¶-r : ā eā eā' eā ā eā ā¶ eā' ā eā - eā ā¶ eā - eā'
  ā¶if : ā eā eā' eā eā ā eā ā¶ eā' ā if eā then eā else eā ā¶ if eā' then eā else eā

data _ā¶*_ : term ā term ā Set where

  ā¶*refl : ā {e} ā
        e ā¶* e
  ā¶*sing : ā {eā eā} ā
        eā ā¶ eā
        -----------------
     ā eā ā¶* eā
  ā¶*cat : ā {eā eā eā} ā
        eā ā¶* eā
     ā eā ā¶* eā
       ---------------
     ā eā ā¶* eā

  -- TODO use Relation.Binary.Construct.Closure.ReflexiveTransitive.star

ā¶*+l : ā {eā eā' eā} ā eā ā¶* eā' ā (eā + eā) ā¶* (eā' + eā)
ā¶*+l ā¶*refl = ā¶*refl
ā¶*+l (ā¶*sing x) = ā¶*sing (ā¶+l _ _ _ x) 
ā¶*+l (ā¶*cat p pā) = ā¶*cat (ā¶*+l p) (ā¶*+l pā)

ā¶*+r : ā {eā eā eā'} ā eā ā¶* eā' ā (eā + eā) ā¶* (eā + eā')
ā¶*+r ā¶*refl = ā¶*refl
ā¶*+r (ā¶*sing x) = ā¶*sing (ā¶+r _ _ _ x)
ā¶*+r (ā¶*cat p pā) = ā¶*cat (ā¶*+r p) (ā¶*+r pā)

ā¶*-l : ā {eā eā' eā} ā eā ā¶* eā' ā (eā - eā) ā¶* (eā' - eā)
ā¶*-l ā¶*refl = ā¶*refl
ā¶*-l (ā¶*sing x) = ā¶*sing (ā¶-l _ _ _ x) 
ā¶*-l (ā¶*cat p pā) = ā¶*cat (ā¶*-l p) (ā¶*-l pā)

ā¶*-r : ā {eā eā eā'} ā eā ā¶* eā' ā (eā - eā) ā¶* (eā - eā')
ā¶*-r ā¶*refl = ā¶*refl
ā¶*-r (ā¶*sing x) = ā¶*sing (ā¶-r _ _ _ x)
ā¶*-r (ā¶*cat p pā) = ā¶*cat (ā¶*-r p) (ā¶*-r pā)

ā¶*if : ā {eā eā' eā eā} ā eā ā¶* eā' ā (if eā then eā else eā) ā¶* (if eā' then eā else eā)
ā¶*if ā¶*refl = ā¶*refl
ā¶*if (ā¶*sing x) = ā¶*sing (ā¶if _ _ _ _ x)
ā¶*if (ā¶*cat p pā) = ā¶*cat (ā¶*if p) (ā¶*if pā)

data _val : term ā Set where

  tru-val : tru val
  fls-val : fls val
  n-val : ā n ā [ n ] val

Value = Ī£ term (Ī» e ā e val)

data š±ā¦Boolā§ : term ā Set where
  tru-bool : š±ā¦Boolā§ tru
  fls-bool : š±ā¦Boolā§ fls

data š±ā¦Natā§ : term ā Set where
  n-nat : ā n ā š±ā¦Natā§ [ n ]

š±ā¦_ā§ : type ā term ā Set
š±ā¦ Bool ā§ = š±ā¦Boolā§
š±ā¦ Nat ā§ = š±ā¦Natā§

-- š±ā¦_ā§ : type ā Set
-- š±ā¦ Bool ā§ = Ī£ term š±ā¦Boolā§
-- š±ā¦ Nat ā§ = Ī£ term š±ā¦Natā§

ā°ā¦_ā§ : type ā term ā Set
ā°ā¦ Ļ ā§ e = Ī£[ v ā term ] ((e ā¶* v)  Ć  (š±ā¦ Ļ ā§ v))

infix 18 beginā¶*_
beginā¶*_ : ā {eā eā} ā eā ā¶* eā ā eā ā¶* eā
beginā¶* eāā¶*eā = eāā¶*eā

infix 22 _qed
_qed : ā e ā e ā¶* e
e qed = ā¶*refl {e}

infixr 20 _ā¶*āØ_ā©_
_ā¶*āØ_ā©_ : ā eā ā ā {eā eā} ā eā ā¶* eā ā eā ā¶* eā ā eā ā¶* eā
eā ā¶*āØ eāā¶*eā ā© eāā¶*eā = ā¶*cat eāā¶*eā eāā¶*eā

fp : ā {e Ļ} ā ā¢ e ā¶ Ļ ā ā°ā¦ Ļ ā§ e
fp (INat n) = [ n ] , ā¶*refl , n-nat n
fp IBoolT = tru , ā¶*refl , tru-bool
fp IBoolF = fls , ā¶*refl , fls-bool
fp (ENat+ eā eā tyā tyā) with fp tyā | fp tyā
... | [ nā ] , eāā¶*vā , n-nat nā
    | [ nā ] , eāā¶*vā , n-nat nā
    = [ nā Data.Nat.+ nā ] , eā+eāā¶*nā+nā , n-nat (nā Data.Nat.+ nā) where
  eā+eāā¶*nā+nā : (eā + eā) ā¶* [ nā Data.Nat.+ nā ]
  eā+eāā¶*nā+nā = beginā¶*
      (eā + eā)
    ā¶*āØ ā¶*+l eāā¶*vā  ā©
      ([ nā ] + eā)
    ā¶*āØ ā¶*+r eāā¶*vā  ā©
      ([ nā ] + [ nā ])
    ā¶*āØ ā¶*sing (ā¶+ nā nā) ā©
      [ nā Data.Nat.+ nā ]
    qed
fp (ENat- eā eā tyā tyā) with fp tyā | fp tyā
... | [ nā ] , eāā¶*vā , n-nat nā
    | [ nā ] , eāā¶*vā , n-nat nā
    = [ nā Data.Nat.āø nā ] , eā-eāā¶*nāāønā , n-nat (nā Data.Nat.āø nā) where
  eā-eāā¶*nāāønā : (eā - eā) ā¶* [ nā Data.Nat.āø nā ]
  eā-eāā¶*nāāønā = beginā¶*
      (eā - eā)
    ā¶*āØ ā¶*-l eāā¶*vā  ā©
      ([ nā ] - eā)
    ā¶*āØ ā¶*-r eāā¶*vā  ā©
      ([ nā ] - [ nā ])
    ā¶*āØ ā¶*sing (ā¶- nā nā) ā©
      [ nā Data.Nat.āø nā ]
    qed
fp (IIf eā eā eā _ tyā tyā tyā) with fp tyā | fp tyā | fp tyā
... | .tru , eāā¶*tru , tru-bool | v , eāā¶*v , vāĻ | _
    =  v ,  beginā¶*
              (if eā then eā else eā)
            ā¶*āØ ā¶*if eāā¶*tru ā©
              (if tru then eā else eā)
            ā¶*āØ ā¶*sing ā¶tru ā©
              eā
            ā¶*āØ eāā¶*v ā©
              v
            qed
         , vāĻ
... | .fls , eāā¶*fls , fls-bool | _ | v , eāā¶*v , vāĻ
    =  v ,  beginā¶*
              (if eā then eā else eā)
            ā¶*āØ ā¶*if eāā¶*fls ā©
              (if fls then eā else eā)
            ā¶*āØ ā¶*sing ā¶fls ā©
              eā
            ā¶*āØ eāā¶*v ā©
              v
            qed
         , vāĻ

_ā_ : ā {eā eā Ļ} ā ā¢ eā ā¶ Ļ ā ā¢ eā ā¶ Ļ ā Set
tā ā tā = projā (fp tā) ā” projā (fp tā)

-- todo check that this should be called reify
reify? : ā {Ļ} ā šÆā¦ Ļ ā§ ā term
reify? {Bool} š¹.false = fls
reify? {Bool} š¹.true = tru
reify? {Nat} n = [ n ]

reify?-injective : ā {Ļ} ā ā (vā vā : šÆā¦ Ļ ā§) ā reify? vā ā” reify? vā ā vā ā” vā
reify?-injective {Bool} š¹.false š¹.false reify?vāā”reify?vā = refl
reify?-injective {Bool} š¹.true š¹.true reify?vāā”reify?vā = refl
reify?-injective {Nat} vā vā refl = refl

[-]-injective : ā {m n} ā [ m ] ā” [ n ] ā m ā” n
[-]-injective refl = refl

truā”reify?ā¦_ā§_ : ā {e} ā (t : ā¢ e ā¶ Bool) ā tru ā” reify? ā¦ t ā§ ā ā¦ t ā§ ā” š¹.true
truā”reify?ā¦ t ā§ p with ā¦ t ā§
... | š¹.true = refl

flsā”reify?ā¦_ā§_ : ā {e} ā (t : ā¢ e ā¶ Bool) ā fls ā” reify? ā¦ t ā§ ā ā¦ t ā§ ā” š¹.false
flsā”reify?ā¦ t ā§ p with ā¦ t ā§
... | š¹.false = refl

thing : ā {e Ļ} ā (t : ā¢ e ā¶ Ļ) ā projā (fp t) ā” reify? ā¦ t ā§
thing (INat n) = refl
thing IBoolT = refl
thing IBoolF = refl
thing (ENat+ eā eā tā tā) with fp tā | fp tā | thing tā | thing tā
... | .([ n ]) , fstā , n-nat n | .([ nā ]) , fstā , n-nat nā | p | q rewrite [-]-injective p | [-]-injective q = refl
thing (ENat- eā eā tā tā) with fp tā | fp tā | thing tā | thing tā
... | .([ n ]) , fstā , n-nat n | .([ nā ]) , fstā , n-nat nā | p | q rewrite [-]-injective p | [-]-injective q = refl
thing (IIf eā eā eā _ tā tā tā) with fp tā | thing tā
... | .tru , q , tru-bool | s rewrite truā”reify?ā¦ tā ā§ s = thing tā
... | .fls , q , fls-bool | s rewrite flsā”reify?ā¦ tā ā§ s = thing tā

soundness : ā {eā eā Ļ} ā (tā : ā¢ eā ā¶ Ļ) ā (tā : ā¢ eā ā¶ Ļ) ā tā ā tā ā ā¦ tā ā§ ā” ā¦ tā ā§
soundness tā tā tāātā = reify?-injective ā¦ tā ā§ ā¦ tā ā§ (begin
    reify? ā¦ tā ā§
  ā”āØ Eq.sym (thing tā) ā©
    projā (fp tā)
  ā”āØ tāātā ā©
    projā (fp tā)
  ā”āØ thing tā ā©
    reify? ā¦ tā ā§
  ā)

adequacy : ā {eā eā Ļ} ā (tā : ā¢ eā ā¶ Ļ) ā (tā : ā¢ eā ā¶ Ļ) ā ā¦ tā ā§ ā” ā¦ tā ā§ ā tā ā tā
adequacy tā tā ā¦tāā§ā”ā¦tāā§ = begin
    projā (fp tā)
  ā”āØ thing tā ā©
    reify? ā¦ tā ā§
  ā”āØ Eq.cong reify? ā¦tāā§ā”ā¦tāā§ ā©
    reify? ā¦ tā ā§
  ā”āØ Eq.sym (thing tā) ā©
    projā (fp tā)
  ā
```
