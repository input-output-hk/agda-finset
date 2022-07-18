{-# OPTIONS --safe #-}

module Utilities.FinProperties where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  hiding (inspect)
open import Relation.Binary.Core
open import Relation.Nullary

open import Data.Bool hiding (_≟_)
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
open import Data.List
open import Data.List.Properties
open import Data.Fin
  hiding ( _≤_ ; _<_)
  renaming (suc to fsuc ; zero to fzero ; pred to fpred)
open import Data.Empty
open import Data.Nat
open import Data.Unit hiding (_≟_)
open import Data.Vec
  renaming (map to vmap ; _++_ to _++v_ ; _∷_ to _::_)
  hiding (drop ; take ; foldl ; foldr ; length ; allFin)
open import Data.Vec.Membership.Propositional
  renaming (_∈_ to _∈v_)
open import Data.List.Membership.Propositional.Properties
open import Data.Vec.Membership.Propositional.Properties
open import Data.Vec.Relation.Unary.Any hiding (map)
open import Function using (id)

open import Data.Vec.Properties hiding (map-cong)
open import Utilities.ListProperties
open import Utilities.ListsAddition
open import Utilities.Logic



allFinList : ∀ n → List (Fin n)
allFinList n = allFin n

toListC : {X : Set} → {n : ℕ} → (i : X) → (v : Vec X n)
  → i ∈v v → i ∈ toList v
toListC i _ (here px) rewrite px = here refl
toListC i _ (there h) = there (toListC i _ h)

allFinListComplete : ∀ {n} → (i : Fin n) → i ∈ allFinList n
allFinListComplete = ∈-allFin

allFinList-fromVec : ∀ {n} → allFinList n ≡ toList (Data.Vec.allFin n)
allFinList-fromVec {zero} = refl
allFinList-fromVec {suc n} rewrite sym (allFinList-fromVec {n}) = cong (fzero ∷_) (begin
  Data.List.tabulate fsuc
    ≡˘⟨ map-tabulate id fsuc ⟩
  map fsuc (Data.List.tabulate id)
    ≡⟨ cong (map fsuc) (allFinList-fromVec {n}) ⟩
  map fsuc (toList (Data.Vec.tabulate id))
    ≡⟨ map-toList fsuc (Data.Vec.tabulate id) ⟩
  toList (vmap fsuc (Data.Vec.tabulate id))
    ≡˘⟨ cong toList (tabulate-∘ fsuc id) ⟩
  toList (Data.Vec.tabulate fsuc) ∎)
  where
    open ≡-Reasoning

    map-toList : ∀ {X Y : Set} {n : ℕ} (f : X → Y) (v : Vec X n) → map f (toList v) ≡ toList (vmap f v)
    map-toList f [] = refl
    map-toList f (x :: v) = cong (f x ∷_) (map-toList f v)

convf : {X : Set} → (xs : List X) → Σ[ x ∈ X ] x ∈ xs → Fin (length xs)
convf ._ (proj₁ , (here refl)) = fzero
convf ._ (x , there proj₂) = fsuc (convf _ (x , proj₂))

convb : {X : Set} → (xs : List X) → Fin (length xs) → Σ[ x ∈ X ] x ∈ xs
convb [] ()
convb (x ∷ xs) fzero = x , here refl
convb (x ∷ xs) (fsuc f) = proj₁ (convb xs f) , there (proj₂ (convb xs f))

convfb : {X : Set} → (xs : List X) → (f : Fin (length xs)) → convf xs (convb xs f) ≡ f
convfb [] ()
convfb (x ∷ xs) fzero = refl
convfb (x ∷ xs) (fsuc f) = cong fsuc (convfb  xs f)

convbf : {X : Set} → (xs : List X) → (xi : Σ[ x ∈ X ] x ∈ xs) → convb xs (convf xs xi) ≡ xi
convbf [] (proj₁ , ())
convbf (x ∷ xs) (.x , (here refl)) = refl
convbf (x ∷ xs) (x₁ , there proj₂) with convbf xs (x₁ , proj₂)
... | o rewrite o = refl
