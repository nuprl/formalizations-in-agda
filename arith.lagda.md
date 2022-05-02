
```
module Arith where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
import Data.Bool as 𝔹

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
interp [ n ]' = {!!}
interp tru' = {!!}
interp fls' = {!!}
interp (e +' e₁) = {!!}
interp (e -' e₁) = {!!}
interp (if' e then e₁ else e₂) = {!!}
```
