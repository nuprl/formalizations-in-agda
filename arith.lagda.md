```
module arith where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
import Data.Bool as 𝔹

-- open import Agda.Builtin.Sigma
open import Data.Product
```

The syntax of arithmetic expressions.

```
data term : Set where

  [_] :
      (n : ℕ)
      -------
    → term

  tru : term

  fls : term

  _+_ :
     term → term → term

  _-_ :
     term → term → term

  if_then_else_ :
     term → term → term → term

ex : term
ex = [ 3 ] + [ 4 ]

ex2 : term
ex2 = if tru then [ 3 ] else fls

data type : Set where

  Bool : type
  Nat : type

data ⊢'_ : type → Set where
  [_]' :
      (n : ℕ)
      -------------
    → ⊢' Nat

  tru' :
      ------------
      ⊢' Bool

  fls' :
      ------------
      ⊢' Bool

  _+'_ :
      ⊢' Nat
    → ⊢' Nat
      --------------
    → ⊢' Nat

  _-'_ :
      ⊢' Nat
    → ⊢' Nat
      --------------
    → ⊢' Nat

  if'_then_else_ : {τ : type}
    → ⊢' Bool
    → ⊢' τ
    → ⊢' τ
      ---------------------------
    → ⊢' τ


data ⊢_∶_ : term → type → Set where

  INat :
      (n : ℕ)
      -------------
    → ⊢ [ n ] ∶ Nat

  IBoolT :
      ------------
      ⊢ tru ∶ Bool

  IBoolF :
      ------------
      ⊢ fls ∶ Bool

  ENat+ :
      (e₁ e₂ : term)
    → ⊢ e₁ ∶ Nat
    → ⊢ e₂ ∶ Nat
      --------------
    → ⊢ e₁ + e₂ ∶ Nat

  ENat- :
      (e₁ e₂ : term)
    → ⊢ e₁ ∶ Nat
    → ⊢ e₂ ∶ Nat
      --------------
    → ⊢ e₁ - e₂ ∶ Nat

  IIf :
      (e₁ e₂ e₃ : term) (τ : type)
    → ⊢ e₁ ∶ Bool
    → ⊢ e₂ ∶ τ
    → ⊢ e₃ ∶ τ
      ---------------------------
    → ⊢ if e₁ then e₂ else e₃ ∶ τ

𝒯⟦_⟧ : type → Set
𝒯⟦ Bool ⟧ =  𝔹.Bool
𝒯⟦ Nat ⟧ =  ℕ

⟦_⟧ : {e : term} {τ : type} → ⊢ e ∶ τ → 𝒯⟦ τ ⟧
⟦ INat n ⟧ =  n
⟦ IBoolT ⟧ =  𝔹.true
⟦ IBoolF ⟧ =  𝔹.false
⟦ ENat+ e₁ e₂ tj tj₁ ⟧ = ⟦ tj ⟧ Data.Nat.+ ⟦ tj₁ ⟧
⟦ ENat- e₁ e₂ tj tj₁ ⟧ = ⟦ tj ⟧ Data.Nat.∸ ⟦ tj₁ ⟧
⟦ IIf e₁ e₂ e₃ _ tj tj₁ tj₂ ⟧ = 𝔹.if ⟦ tj ⟧ then ⟦ tj₁ ⟧ else ⟦ tj₂ ⟧

test : (e : term) (t : type) {{prf : ⊢ e ∶ t}} -> ⊢ e ∶ t
test e t {{prf}} = prf

test2 : ⊢' Nat
test2 = [ 0 ]' +' [ 1 ]'

interp : {τ : type} → ⊢' τ → 𝒯⟦ τ ⟧
interp [ n ]' = n
interp tru' =  𝔹.true
interp fls' =  𝔹.false
interp (e +' e₁) = interp e Data.Nat.+ interp e₁
interp (e -' e₁) = interp e Data.Nat.∸ interp e₁
interp (if' e then e₁ else e₂) = 𝔹.if (interp e) then interp e₁ else interp e₂
```

# Operational semantics of arith

```
infix 18 _⟶_
data _⟶_ : term → term → Set where

  ⟶+ : ∀ m n → [ n ] + [ m ] ⟶ [ n Data.Nat.+ m ]
  ⟶- : ∀ m n → [ n ] - [ m ] ⟶ [ n Data.Nat.∸ m ]
  ⟶tru : ∀ {e₁ e₂} → if tru then e₁ else e₂ ⟶ e₁
  ⟶fls : ∀ {e₁ e₂} → if fls then e₁ else e₂ ⟶ e₂

  ⟶+l : ∀ e₁ e₁' e₂ →
       e₁ ⟶ e₁'
       -----------------
    → e₁ + e₂ ⟶ e₁' + e₂

  ⟶+r : ∀ e₁ e₂' e₂ →
       e₂ ⟶ e₂'
       ---------------------
    → e₁ + e₂ ⟶ e₁ + e₂'

  ⟶-l : ∀ e₁ e₁' e₂ → e₁ ⟶ e₁' → e₁ - e₂ ⟶ e₁' - e₂
  ⟶-r : ∀ e₁ e₂' e₂ → e₂ ⟶ e₂' → e₁ - e₂ ⟶ e₁ - e₂'
  ⟶if : ∀ e₁ e₁' e₂ e₃ → e₁ ⟶ e₁' → if e₁ then e₂ else e₃ ⟶ if e₁' then e₂ else e₃

data _⟶*_ : term → term → Set where

  ⟶*refl : ∀ {e} →
        e ⟶* e
  ⟶*sing : ∀ {e₁ e₂} →
        e₁ ⟶ e₂
        -----------------
     → e₁ ⟶* e₂
  ⟶*cat : ∀ {e₁ e₂ e₃} →
        e₁ ⟶* e₂
     → e₂ ⟶* e₃
       ---------------
     → e₁ ⟶* e₃

  -- TODO use Relation.Binary.Construct.Closure.ReflexiveTransitive.star

⟶*+l : ∀ {e₁ e₁' e₂} → e₁ ⟶* e₁' → (e₁ + e₂) ⟶* (e₁' + e₂)
⟶*+l ⟶*refl = ⟶*refl
⟶*+l (⟶*sing x) = ⟶*sing (⟶+l _ _ _ x) 
⟶*+l (⟶*cat p p₁) = ⟶*cat (⟶*+l p) (⟶*+l p₁)

⟶*+r : ∀ {e₁ e₂ e₂'} → e₂ ⟶* e₂' → (e₁ + e₂) ⟶* (e₁ + e₂')
⟶*+r ⟶*refl = ⟶*refl
⟶*+r (⟶*sing x) = ⟶*sing (⟶+r _ _ _ x)
⟶*+r (⟶*cat p p₁) = ⟶*cat (⟶*+r p) (⟶*+r p₁)

⟶*-l : ∀ {e₁ e₁' e₂} → e₁ ⟶* e₁' → (e₁ - e₂) ⟶* (e₁' - e₂)
⟶*-l ⟶*refl = ⟶*refl
⟶*-l (⟶*sing x) = ⟶*sing (⟶-l _ _ _ x) 
⟶*-l (⟶*cat p p₁) = ⟶*cat (⟶*-l p) (⟶*-l p₁)

⟶*-r : ∀ {e₁ e₂ e₂'} → e₂ ⟶* e₂' → (e₁ - e₂) ⟶* (e₁ - e₂')
⟶*-r ⟶*refl = ⟶*refl
⟶*-r (⟶*sing x) = ⟶*sing (⟶-r _ _ _ x)
⟶*-r (⟶*cat p p₁) = ⟶*cat (⟶*-r p) (⟶*-r p₁)

⟶*if : ∀ {e₁ e₁' e₂ e₃} → e₁ ⟶* e₁' → (if e₁ then e₂ else e₃) ⟶* (if e₁' then e₂ else e₃)
⟶*if ⟶*refl = ⟶*refl
⟶*if (⟶*sing x) = ⟶*sing (⟶if _ _ _ _ x)
⟶*if (⟶*cat p p₁) = ⟶*cat (⟶*if p) (⟶*if p₁)

data _val : term → Set where

  tru-val : tru val
  fls-val : fls val
  n-val : ∀ n → [ n ] val

Value = Σ term (λ e → e val)

data 𝒱⟦Bool⟧ : term → Set where
  tru-bool : 𝒱⟦Bool⟧ tru
  fls-bool : 𝒱⟦Bool⟧ fls

data 𝒱⟦Nat⟧ : term → Set where
  n-nat : ∀ n → 𝒱⟦Nat⟧ [ n ]

𝒱⟦_⟧ : type → term → Set
𝒱⟦ Bool ⟧ = 𝒱⟦Bool⟧
𝒱⟦ Nat ⟧ = 𝒱⟦Nat⟧

-- 𝒱⟦_⟧ : type → Set
-- 𝒱⟦ Bool ⟧ = Σ term 𝒱⟦Bool⟧
-- 𝒱⟦ Nat ⟧ = Σ term 𝒱⟦Nat⟧

ℰ⟦_⟧ : type → term → Set
ℰ⟦ τ ⟧ e = Σ[ v ∈ term ] ((e ⟶* v)  ×  (𝒱⟦ τ ⟧ v))

infix 18 begin⟶*_
begin⟶*_ : ∀ {e₁ e₂} → e₁ ⟶* e₂ → e₁ ⟶* e₂
begin⟶* e₁⟶*e₂ = e₁⟶*e₂

infix 22 _qed
_qed : ∀ e → e ⟶* e
e qed = ⟶*refl {e}

infixr 20 _⟶*⟨_⟩_
_⟶*⟨_⟩_ : ∀ e₁ → ∀ {e₂ e₃} → e₁ ⟶* e₂ → e₂ ⟶* e₃ → e₁ ⟶* e₃
e₁ ⟶*⟨ e₁⟶*e₂ ⟩ e₂⟶*e₃ = ⟶*cat e₁⟶*e₂ e₂⟶*e₃

fp : ∀ {e τ} → ⊢ e ∶ τ → ℰ⟦ τ ⟧ e
fp (INat n) = [ n ] , ⟶*refl , n-nat n
fp IBoolT = tru , ⟶*refl , tru-bool
fp IBoolF = fls , ⟶*refl , fls-bool
fp (ENat+ e₁ e₂ ty₁ ty₂) with fp ty₁ | fp ty₂
... | [ n₁ ] , e₁⟶*v₁ , n-nat n₁
    | [ n₂ ] , e₂⟶*v₂ , n-nat n₂
    = [ n₁ Data.Nat.+ n₂ ] , e₁+e₂⟶*n₁+n₂ , n-nat (n₁ Data.Nat.+ n₂) where
  e₁+e₂⟶*n₁+n₂ : (e₁ + e₂) ⟶* [ n₁ Data.Nat.+ n₂ ]
  e₁+e₂⟶*n₁+n₂ = begin⟶*
      (e₁ + e₂)
    ⟶*⟨ ⟶*+l e₁⟶*v₁  ⟩
      ([ n₁ ] + e₂)
    ⟶*⟨ ⟶*+r e₂⟶*v₂  ⟩
      ([ n₁ ] + [ n₂ ])
    ⟶*⟨ ⟶*sing (⟶+ n₂ n₁) ⟩
      [ n₁ Data.Nat.+ n₂ ]
    qed
fp (ENat- e₁ e₂ ty₁ ty₂) with fp ty₁ | fp ty₂
... | [ n₁ ] , e₁⟶*v₁ , n-nat n₁
    | [ n₂ ] , e₂⟶*v₂ , n-nat n₂
    = [ n₁ Data.Nat.∸ n₂ ] , e₁-e₂⟶*n₁∸n₂ , n-nat (n₁ Data.Nat.∸ n₂) where
  e₁-e₂⟶*n₁∸n₂ : (e₁ - e₂) ⟶* [ n₁ Data.Nat.∸ n₂ ]
  e₁-e₂⟶*n₁∸n₂ = begin⟶*
      (e₁ - e₂)
    ⟶*⟨ ⟶*-l e₁⟶*v₁  ⟩
      ([ n₁ ] - e₂)
    ⟶*⟨ ⟶*-r e₂⟶*v₂  ⟩
      ([ n₁ ] - [ n₂ ])
    ⟶*⟨ ⟶*sing (⟶- n₂ n₁) ⟩
      [ n₁ Data.Nat.∸ n₂ ]
    qed
fp (IIf e₁ e₂ e₃ _ ty₁ ty₂ ty₃) with fp ty₁ | fp ty₂ | fp ty₃
... | .tru , e₁⟶*tru , tru-bool | v , e₂⟶*v , v∈τ | _
    =  v ,  begin⟶*
              (if e₁ then e₂ else e₃)
            ⟶*⟨ ⟶*if e₁⟶*tru ⟩
              (if tru then e₂ else e₃)
            ⟶*⟨ ⟶*sing ⟶tru ⟩
              e₂
            ⟶*⟨ e₂⟶*v ⟩
              v
            qed
         , v∈τ
... | .fls , e₁⟶*fls , fls-bool | _ | v , e₃⟶*v , v∈τ
    =  v ,  begin⟶*
              (if e₁ then e₂ else e₃)
            ⟶*⟨ ⟶*if e₁⟶*fls ⟩
              (if fls then e₂ else e₃)
            ⟶*⟨ ⟶*sing ⟶fls ⟩
              e₃
            ⟶*⟨ e₃⟶*v ⟩
              v
            qed
         , v∈τ

_≃_ : ∀ {e₁ e₂ τ} → ⊢ e₁ ∶ τ → ⊢ e₂ ∶ τ → Set
t₁ ≃ t₂ = proj₁ (fp t₁) ≡ proj₁ (fp t₂)

-- todo check that this should be called reify
reify? : ∀ {τ} → 𝒯⟦ τ ⟧ → term
reify? {Bool} 𝔹.false = fls
reify? {Bool} 𝔹.true = tru
reify? {Nat} n = [ n ]

reify?-injective : ∀ {τ} → ∀ (v₁ v₂ : 𝒯⟦ τ ⟧) → reify? v₁ ≡ reify? v₂ → v₁ ≡ v₂
reify?-injective {Bool} 𝔹.false 𝔹.false reify?v₁≡reify?v₂ = refl
reify?-injective {Bool} 𝔹.true 𝔹.true reify?v₁≡reify?v₂ = refl
reify?-injective {Nat} v₁ v₂ refl = refl

[-]-injective : ∀ {m n} → [ m ] ≡ [ n ] → m ≡ n
[-]-injective refl = refl

tru≡reify?⟦_⟧_ : ∀ {e} → (t : ⊢ e ∶ Bool) → tru ≡ reify? ⟦ t ⟧ → ⟦ t ⟧ ≡ 𝔹.true
tru≡reify?⟦ t ⟧ p with ⟦ t ⟧
... | 𝔹.true = refl

fls≡reify?⟦_⟧_ : ∀ {e} → (t : ⊢ e ∶ Bool) → fls ≡ reify? ⟦ t ⟧ → ⟦ t ⟧ ≡ 𝔹.false
fls≡reify?⟦ t ⟧ p with ⟦ t ⟧
... | 𝔹.false = refl

thing : ∀ {e τ} → (t : ⊢ e ∶ τ) → proj₁ (fp t) ≡ reify? ⟦ t ⟧
thing (INat n) = refl
thing IBoolT = refl
thing IBoolF = refl
thing (ENat+ e₁ e₂ t₁ t₂) with fp t₁ | fp t₂ | thing t₁ | thing t₂
... | .([ n ]) , fst₁ , n-nat n | .([ n₁ ]) , fst₃ , n-nat n₁ | p | q rewrite [-]-injective p | [-]-injective q = refl
thing (ENat- e₁ e₂ t₁ t₂) with fp t₁ | fp t₂ | thing t₁ | thing t₂
... | .([ n ]) , fst₁ , n-nat n | .([ n₁ ]) , fst₃ , n-nat n₁ | p | q rewrite [-]-injective p | [-]-injective q = refl
thing (IIf e₁ e₂ e₃ _ t₁ t₂ t₃) with fp t₁ | thing t₁
... | .tru , q , tru-bool | s rewrite tru≡reify?⟦ t₁ ⟧ s = thing t₂
... | .fls , q , fls-bool | s rewrite fls≡reify?⟦ t₁ ⟧ s = thing t₃

soundness : ∀ {e₁ e₂ τ} → (t₁ : ⊢ e₁ ∶ τ) → (t₂ : ⊢ e₂ ∶ τ) → t₁ ≃ t₂ → ⟦ t₁ ⟧ ≡ ⟦ t₂ ⟧
soundness t₁ t₂ t₁≃t₂ = reify?-injective ⟦ t₁ ⟧ ⟦ t₂ ⟧ (begin
    reify? ⟦ t₁ ⟧
  ≡⟨ Eq.sym (thing t₁) ⟩
    proj₁ (fp t₁)
  ≡⟨ t₁≃t₂ ⟩
    proj₁ (fp t₂)
  ≡⟨ thing t₂ ⟩
    reify? ⟦ t₂ ⟧
  ∎)

adequacy : ∀ {e₁ e₂ τ} → (t₁ : ⊢ e₁ ∶ τ) → (t₂ : ⊢ e₂ ∶ τ) → ⟦ t₁ ⟧ ≡ ⟦ t₂ ⟧ → t₁ ≃ t₂
adequacy t₁ t₂ ⟦t₁⟧≡⟦t₂⟧ = begin
    proj₁ (fp t₁)
  ≡⟨ thing t₁ ⟩
    reify? ⟦ t₁ ⟧
  ≡⟨ Eq.cong reify? ⟦t₁⟧≡⟦t₂⟧ ⟩
    reify? ⟦ t₂ ⟧
  ≡⟨ Eq.sym (thing t₂) ⟩
    proj₁ (fp t₂)
  ∎
```
