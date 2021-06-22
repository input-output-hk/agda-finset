module Utilities.ArithmeticProperties where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat using (_<_) public
open import Data.Nat.Properties
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; n∸n≡0) public
open import Data.Sum

+-comm-sum : ∀ {a b c} → a + b ≡ c → b + a ≡ c
+-comm-sum {a} {b} {c} eq rewrite +-comm a b = eq

≤-pr : ∀ a b → a ≤ b ⊎ b ≤ a
≤-pr a b = map₁ <⇒≤ (<-≤-connex a b)

<-weak : ∀ a b  → (suc a) < b → a < b
<-weak a b h = m+n≤o⇒n≤o 1 h

<-cong2 : ∀ {k n} → suc k < suc n → k < n
<-cong2 (s≤s h) = h
