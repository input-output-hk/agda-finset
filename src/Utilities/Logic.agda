module Utilities.Logic where

open import Data.Nat
open import Data.List
open import Data.Empty

open import Relation.Binary.PropositionalEquality public

open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Decidable using (isYes) public
open import Data.Empty using (⊥-elim) public
open import Data.Unit
open import Data.Bool



DecEq : ∀ X → Set
DecEq = DecidableEquality


DecEqRest : {X : Set} → (P : X → Set) → Set
DecEqRest P = ∀ x1 x2 → P x1 → P x2 → Dec (x1 ≡ x2)


∥_∥ : ∀ {p} → {S : Set p} → Dec S → Set
∥_∥ = True

∥-∥-prop3 : {S : Set} → (d : Dec S) → ∥ d ∥ → S
∥-∥-prop3 _ = toWitness

∥-∥-yes : {S : Set} → (d : Dec S) → {∥ d ∥} → S
∥-∥-yes _ {d} = toWitness d

∥-∥-prop2 : {S : Set} → S → (d : Dec S) → ∥ d ∥ 
∥-∥-prop2 s _ = fromWitness s

∥-∥-prop : {S : Set} → (d : Dec S) → (s₁ s₂ : ∥ d ∥) → s₁ ≡ s₂
∥-∥-prop (yes p) tt tt = refl
∥-∥-prop (no ¬p) () s2
