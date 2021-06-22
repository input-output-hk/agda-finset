module Utilities.ListProperties where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary.Decidable hiding (map)
open import Data.List hiding (filter) renaming (boolFilter to filter)
open import Data.List.Properties hiding (map-cong)
open import Data.List.Properties using (++-assoc; ++-cancelˡ; map-++-commute; ++-identityʳ) public
open import Data.List.Membership.Propositional public
open import Data.List.Relation.Unary.Any public
  using (Any; here; there; any?)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ʳ; ++⁺ˡ; ++⁻) public
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Data.Empty
open import Data.Nat hiding (_<_)
open import Utilities.Logic
open import Utilities.ArithmeticProperties
open import Data.Sum hiding (map)
open import Level hiding (suc)
open import Data.List.Relation.Unary.Unique.Propositional renaming (Unique to NoDupInd) public
open import Data.List.Relation.Unary.All.Properties using (All¬⇒¬Any; ¬Any⇒All¬) public

DecIn : ∀ X → Set
DecIn X = Decidable (_∈_ {A = X})

eq2in : {X : Set} → DecEq X → DecIn X
eq2in d x = any? (d x)


in2eq : {X : Set} → DecIn X → DecEq X
in2eq ∈? x1 y1 with ∈? x1 (y1 ∷ [])
... | yes (here px) = yes px
... | no ¬p = no (λ pr → ¬p (subst (λ h → x1 ∈ (h ∷ [])) pr (here refl)))


NoDup : {a : Level} {X : Set a} → List X → Set a
NoDup {X = X} xs = (x : X) → x ∈ xs → Σ[ ys ∈ List X ] 
                                    Σ[ zs ∈ List X ] 
                                    xs ≡ ys ++ x ∷ zs × 
                                    ¬ x ∈ ys × 
                                    ¬ x ∈ zs


NoDupInd-corr : {X : Set} → (xs : List X) → NoDupInd xs → NoDup xs
NoDupInd-corr (x ∷ xs) (x₁ ∷ _) x₂ (here h) rewrite h = [] , xs , refl , (λ ()) , All¬⇒¬Any x₁
NoDupInd-corr (x ∷ xs) (x₁ ∷ h) x₂ (there h') with NoDupInd-corr xs h x₂ h'
... | o1 , o2 , o3 , o4 , o5 = x ∷ o1 , o2 , cong (_∷_ x) o3 , helper x x₂ xs o1 h' (All¬⇒¬Any x₁) o4 , o5
  where
    helper : {X : Set} → (x x₂ : X) → (xs o1 : List X) 
     → x₂ ∈ xs → (x ∈ xs → ⊥) → (x₂ ∈ o1 → ⊥) →  x₂ ∈ (x ∷ o1) → ⊥
    helper x₄ x₅ xs₁ o6 xin xinn xinn2 (here h) rewrite h = xinn xin
    helper x₄ x₅ xs₁ o6 xin xinn xinn2 (there xin2) = xinn2 xin2


NoDupInd-pr : {X : Set} → (x : X) → (xs : List X) → (p1 p2 : x ∈ xs) → NoDupInd xs → p1 ≡ p2
NoDupInd-pr x _ (here refl) (here refl) (x₁ ∷ h) = refl
NoDupInd-pr x _ (here refl) (there p2) (x₁ ∷ h) = ⊥-elim (All¬⇒¬Any x₁ p2)
NoDupInd-pr x _ (there p1) (here refl) (x₁ ∷ h) = ⊥-elim  (All¬⇒¬Any x₁ p1)
NoDupInd-pr x _ (there p1) (there p2) (x₁ ∷ h) = cong there (NoDupInd-pr x _ p1 p2 h)

lem : {X : Set} → (x : X) → (xs ys ps : List X)
  →  x ∷ xs ≡ ys ++ x ∷ ps → (x ∈ ys → ⊥) → ys ≡ []
lem x xs [] ps pr1 pr2 = refl
lem x xs (x₁ ∷ ys) ps pr1 pr2 with cong (take 1) pr1 
lem x xs (.x ∷ ys) ps pr1 pr2 | refl with pr2 (here refl)
... | ()

NoDupInd-corr2' : {X : Set} → (xs : List X) → ∀ x → NoDup (x ∷ xs) → NoDup xs 
NoDupInd-corr2' xs x nd  p pin with nd p (there pin)
NoDupInd-corr2' xs x nd .x pin | [] , .xs , refl , q4 , q5 with q5 pin 
... | ()
NoDupInd-corr2' .(q1 ++ p ∷ q2) x nd p pin | .x ∷ q1 , q2 , refl , q4 , q5 = q1 , q2 , refl , (λ pi → q4 (there pi)) , q5

NoDupInd-corr2 : {X : Set} → (xs : List X) → NoDup xs → NoDupInd xs
NoDupInd-corr2 [] nd = []
NoDupInd-corr2 (x ∷ xs) nd with nd x (here refl)
... | ys , ps , z1 , z2 , z3 with lem x xs ys ps z1 z2 
... | ro rewrite ro = ¬Any⇒All¬ xs (λ pr → z3 (subst (λ h → x ∈ h) (cong (drop 1) z1) pr)) ∷ NoDupInd-corr2 _ (NoDupInd-corr2' xs x nd)






list-eq : {C : Set} → Decidable (_≡_ {A = C}) → Decidable (_≡_ {A = List C})
list-eq = ≡-dec



eq-cons : {X : Set} → (x y : X) → (xs ys : List X) → (x Data.List.∷ xs) ≡ (y Data.List.∷ ys) → x ≡ y
eq-cons x .x xs .xs refl = refl



∃-after-map2 : {X Y : Set} → (f : X → Y) → (xs : List X) → (ys1 ys2 : List Y)
  → map f xs ≡ ys1 ++ ys2
  →  Σ[ xs1 ∈ List X ] Σ[ xs2 ∈ List X ] xs1 ++ xs2 ≡ xs × map f xs1 ≡ ys1 × map f xs2 ≡ ys2
∃-after-map2 f xs [] ys2 meq = [] , xs , refl , refl , meq
∃-after-map2 f [] (x ∷ ys1) ys2 ()
∃-after-map2 f (x ∷ xs) (x₁ ∷ ys1) ys2 meq with ∃-after-map2 f xs ys1 ys2 (cong (drop 1) meq) 
... | xs1 , xs2 , xseq , yseq1 , yseq2 with eq-cons (f x) x₁ (map f xs) (ys1 ++ ys2) meq 
... | eq rewrite eq = x ∷ xs1 , xs2 , cong (_∷_ x) xseq , h , yseq2
   where
     h : f x ∷ map f xs1 ≡ x₁ ∷ ys1
     h  = subst (λ h → h ∷ map f xs1 ≡ x₁ ∷ ys1) (sym eq) (cong (_∷_ x₁) yseq1) 


∈len : {X : Set} → {x : X} → {xs : List X} → x ∈ xs → ℕ
∈len (here refl) = 0
∈len (there p) = 1 + ∈len p

∈lenlem : {X : Set} → {x : X} → {xs : List X} 
  → (p1 p2 : x ∈ xs) 
  → ∈len p1 ≡ ∈len p2 → p1 ≡ p2
∈lenlem (here refl) (here refl) prf = refl
∈lenlem (here refl) (there p2) ()
∈lenlem (there p1) (here refl) ()
∈lenlem (there p1) (there p2) prf 
  rewrite ∈lenlem p1 p2  (cong pred prf) = refl

∈-cong : {X Y : Set} → (x : X) → (xs : List X) → (f : X → Y) → x ∈ xs → f x ∈ map f xs
∈-cong x .(_ ∷ _) f (here refl) = here refl
∈-cong x .(_ ∷ _) f (there h) = there (∈-cong x _ f h)

∈-++⁺ʳ-pos : {X : Set}{x : X}(xs₁ xs₂ : List X)
 → (pin : x ∈ xs₂)
 → ∈len (++⁺ʳ xs₁ pin) ≡ (length xs₁) + (∈len pin)
∈-++⁺ʳ-pos [] xs₂ pin = refl
∈-++⁺ʳ-pos (x₁ ∷ xs₁) xs₂ pin = cong suc (∈-++⁺ʳ-pos xs₁ xs₂  pin)

postulate ∈-++⁺ʳ-pos' : {X : Set}{x : X}(xs₁ xs₂ : List X) → (pin : x ∈ xs₂) → ∈len (++⁺ʳ xs₁ pin) ≡ (∈len pin) + (length xs₁)


∈-split : {X : Set} →  {xs₁ xs₂ : List X} → {x : X}
 →  x ∈ (xs₁ ++ xs₂) 
 → (x ∈ xs₁) ⊎ (x ∈ xs₂)
∈-split = ++⁻ _

∈-join : {X : Set} → {xs₁ xs₂ : List X} → {x : X}
 → (x ∈ xs₁) ⊎ (x ∈ xs₂)
 →  x ∈ (xs₁ ++ xs₂) 
∈-join = [ ++⁺ˡ , (++⁺ʳ _) ]′

∃-after-map : {X Y : Set} → (d : X) →  (xs : List X) → (f : X → Y)
 → d ∈ xs → (f d) ∈ (map f xs)
∃-after-map d .(_ ∷ _) f (here refl) = here refl
∃-after-map d .(_ ∷ _) f (there x∈xs) = there (∃-after-map d _ f x∈xs)


∃-split : {X : Set}(x : X)(xs : List X) →  x ∈ xs 
  → Σ[ zs ∈ List X ] Σ[ ds ∈ List X ] xs ≡ zs ++ (x ∷ ds)
∃-split x .(_ ∷ _) (here refl) = [] , _ , refl
∃-split x .(_ ∷ _) (there x∈xs) with ∃-split x _ x∈xs
... | proj₁ , proj₁' , proj₂ = _ ∷ proj₁ , proj₁' , cong (_∷_ _) proj₂

∃-split' : {X : Set}(x : X)(xs : List X) → (pin : x ∈ xs)
  → Σ[ zs ∈ List X ] 
    Σ[ ds ∈ List X ] 
     xs ≡ zs ++ (x ∷ ds) ×
     ∈len pin ≡ length zs
∃-split' x .(_ ∷ _) (here refl) = [] , _ , refl , refl
∃-split' x .(_ ∷ _) (there pin) with ∃-split' x _ pin
... | p1 , p2 , p3 , p4 = _ ∷ p1 , p2 , cong (_∷_ _) p3 , cong suc p4



∈-lst : {X : Set} → (xs : List X)  → List (Σ[ x ∈ X ] x ∈ xs )
∈-lst [] = []
∈-lst (x ∷ xs) 
 = (x , here refl) ∷ map (λ p → (proj₁ p , there (proj₂ p))) (∈-lst xs)

∈-lst-complete : ∀ {X} → (x : X) → (xs : List X) → (prf : (x ∈ xs)) → (x , prf) ∈ (∈-lst xs)
∈-lst-complete x [] ()
∈-lst-complete .x₁ (x₁ ∷ xs) (here refl) = here refl
∈-lst-complete x (x₁ ∷ xs)  (there prf) 
 = there (∈-cong (x , prf) 
         (∈-lst xs) 
         (λ {(p₁ , p₂) → (p₁ , there p₂)}) 
         (∈-lst-complete x xs prf))



foldl-unf : {A B : Set} → (ys : List B) → (l : List A) 
  → (f : A → List B)
  → foldl (λ res el → res ++ f el) ys l ≡ 
      ys ++ foldl (λ res el → res ++ f el  ) [] l
foldl-unf ys [] f =  sym (++-identityʳ _)
foldl-unf ys (x ∷ l) f rewrite 
 foldl-unf (ys ++ f x)  l f 
 | foldl-unf (f x) l f 
 = ++-assoc ys (f x) (foldl (λ res el → res ++ f el) [] l)


-- returning element from the list (with default value)
el : ∀ {X : Set} →  (i : ℕ) → (def : X) → List X → X
el n default [] = default
el zero d (x ∷ xs) = x
el (suc n) d (x ∷ xs) = el n d xs


elth : ∀ {X : Set} → (i : ℕ) → (d e : X) → (ls : List X) 
 → i < length ls → el i d ls ≡ e → e ∈ ls
elth i d e [] () prf
elth zero d e (.e ∷ ls) lss refl = here refl
elth (suc i) d e (x ∷ ls) lss prf = there (elth i d e ls (<-cong2 lss) prf)


alone : ∀ {X : Set} → (e : X) → (e' : X) → e ∈ (e' ∷ []) → e ≡ e'
alone .e' e' (here refl) = refl
alone e e' (there ())





subsetDec' : {X : Set} → (x : X) → (rs : List X) → (eqd : (x y : X) → x ≡ y ⊎ ¬ x ≡ y) → x ∈ rs ⊎ ¬ x ∈ rs
subsetDec' x [] eqd = inj₂ (λ  () )
subsetDec' x (x₁ ∷ rs) eqd with eqd x x₁ 
subsetDec' x (.x ∷ rs) eqd | inj₁ refl = inj₁ (here refl)
subsetDec' x (x₁ ∷ rs) eqd | inj₂ y with subsetDec' x rs eqd 
subsetDec' x (x₂ ∷ rs) eqd | inj₂ y | inj₁ x₁ = inj₁ (there x₁)
subsetDec' x (x₁ ∷ rs) eqd | inj₂ y₁ | inj₂ y = inj₂ (asd  x x₁ rs y₁ y)
  where
    asd : {X : Set} → (x y : X) → (ys : List X) → ¬ x ≡ y → ¬ x ∈ ys → ¬ x ∈ (y ∷ ys)
    asd x₂ .x₂ ys yeq tin (here refl) = yeq refl
    asd x₂ y₂ ys yeq tin (there xin) = tin xin


subsetDec'' : {X : Set} → (x : X) → (rs : List X) → (eqd : (x y : X) → x ≡ y ⊎ ¬ x ≡ y) → Dec (x ∈ rs)
subsetDec'' x rs eqd with subsetDec' x rs eqd 
subsetDec'' x rs eqd | inj₁ x₁ = yes x₁
subsetDec'' x rs eqd | inj₂ y = no y


open import Data.Bool hiding (_≤_)
open import Utilities.Logic 

filter-nest : {X : Set} → (xs : List X)  
 → (p q : X → Bool)
 → filter p (filter q xs) ≡ filter (λ e → p e ∧ q e) xs
filter-nest [] p q = refl
filter-nest (x ∷ xs) p q with q x | inspect q x | p x | inspect p x
... | false | [ eq ] | false | [ eq₁ ] rewrite eq | eq₁ = filter-nest xs p q
... | false | [ eq ] | true | [ eq₁ ] rewrite eq | eq₁ = filter-nest xs p q
... | true | [ eq ] | false | [ eq₁ ] rewrite eq | eq₁ = filter-nest xs p q
... | true | [ eq ] | true | [ eq₁ ] rewrite eq | eq₁ = cong (_∷_ x) (filter-nest xs p q)

filter-id : {X : Set} → (xs : List X) → filter (λ e → true) xs ≡ xs
filter-id [] = refl
filter-id (x ∷ xs) = cong (_∷_ x) (filter-id xs)


filter-∈ : {X : Set} → (x : X) → (xs : List X) → (p : X → Bool) 
  → x ∈ filter p xs → x ∈ xs
filter-∈ x [] p ()
filter-∈ x (x₁ ∷ xs) p pin with p x₁
filter-∈ x₁ (.x₁ ∷ xs) p (here refl) | true = here refl
filter-∈ x (x₁ ∷ xs) p (there pin) | true = there (filter-∈ x xs p  pin)
filter-∈ x (x₁ ∷ xs) p pin | false = there (filter-∈ x xs p pin)


filter-el : {X : Set} → (x : X) → (xs : List X) 
  → (p : X → Bool)
  → x ∈ filter p xs → p x ≡ true
filter-el x [] p ()
filter-el x (x₁ ∷ xs) p xin with p x₁ | inspect p x₁
... | false | _ = filter-el x xs p xin
... | true | [ eq ] with xin
... | here refl = eq
... | there h = filter-el x xs p h


filter-in2 : {X : Set} → (xs : List X) → ∀ x → (p : X → Bool) → x ∈ xs → p x ≡ true → x ∈ filter p xs
filter-in2 [] x p () px
filter-in2 (x ∷ xs) .x p (here refl) px rewrite px = here refl
filter-in2 (x ∷ xs) x₁ p (there xin) px with p x 
filter-in2 (x ∷ xs) x₁ p (there xin) px | true = there (filter-in2 xs x₁ p xin px)
filter-in2 (x ∷ xs) x₁ p (there xin) px | false = (filter-in2 xs x₁ p xin px)


emptDec : {X : Set} → (xs : List X) → Dec (xs ≡ [])
emptDec [] = yes refl
emptDec (x ∷ xs) = no (λ { () })



any-prop : {X : Set} → (p : X → Bool)
 → (ys₁ ys₂ xs₁ xs₂ : List X)
 → (x y : X)
 →  ys₁ ++ y ∷ ys₂ ≡ xs₁ ++ x ∷ xs₂
 → any p ys₁ ≡ false
 → any p xs₁ ≡ false
 → p y ≡ true
 → p x ≡ true
 → ys₁ ≡ xs₁
any-prop p [] ys2 [] xs2 x y pr anp1 refl py px = refl
any-prop p (x ∷ ys1) ys2 [] xs2 x₁ y pr anp1 refl py px with cong (λ { (z ∷ zs) → z ; [] → x  }) pr  
... | x=x1 rewrite x=x1 | px with anp1
... | ()
any-prop p [] ys2 (x ∷ xs1) xs2 x₁ y pr refl anyp py px with cong (λ { (z ∷ zs) → z ; [] → x  }) pr 
... | x=y rewrite x=y | py with anyp
... | ()
any-prop p (x ∷ ys1) ys2 (x₁ ∷ xs1) xs2 x₂ y pr anp1 anyp py px rewrite cong (λ { (z ∷ zs) → z ; [] → x  }) pr = cong (_∷_ x₁) (any-prop p ys1 ys2 xs1 xs2 x₂ y (cong (drop 1) pr) (any-h p ys1  x anp1) (any-h p xs1 x₁ anyp) py px)
  where
    any-h : {X : Set} → (p : X → Bool) → (xs : List X) → ∀ x → any p (x ∷ xs) ≡ false → any p xs ≡ false
    any-h p xs x pr with p x
    any-h p₁ xs x₃ () | true
    any-h p₁ xs x₃ pr₁ | false = pr₁




_SubSetOf_ : ∀ {A : Set} → List A → List A → Set
as₁ SubSetOf as₂ = ∀ {a} → a ∈ as₁ → a ∈ as₂


subset-dec : {X : Set}
  → Decidable (_≡_ {A = X})
  → Decidable (_SubSetOf_ {A = X}) 
subset-dec  eqd [] rs2 = yes (λ () )
subset-dec {_} eqd (x ∷ rs1) rs2 with eq2in eqd x rs2
subset-dec {X} eqd (x ∷ rs1) rs2 |  yes x₁ with subset-dec eqd rs1 rs2 
subset-dec {X} eqd (x₁ ∷ rs1) rs2 | yes x₂ | yes x = yes asd
  where
    asd : {a : X} → a ∈ (x₁ ∷ rs1) → a ∈ rs2
    asd (here refl) = x₂
    asd {a} (there ain) = x {a} ain
subset-dec {X} eqd (x ∷ rs1) rs2  | yes x₁ | no y = no (λ q → y (asd q))
  where
    asd : ({a : X} → a ∈ (x ∷ rs1) → a ∈ rs2) 
      → {a : X} → a ∈ rs1 → a ∈ rs2
    asd prop {a} ain = prop {a} (there ain)
subset-dec  {_} eqd (x ∷ rs1) rs2  | no y = no (λ q → y (q {x} (here refl)))



map-cong : {X Y : Set} → (f : X → Y) →  ∀ x xs → x ∈ xs → f x ∈ map f xs
map-cong f x ._ (here refl) = here refl
map-cong f x ._ (there xin) = there (map-cong f x _ xin)

map-pr1 : {X Y : Set} → (xs : List X)  → (f : X → Y) → (map proj₁ (map (λ x → x , f x) xs)) ≡ xs
map-pr1 [] f = refl
map-pr1 (x ∷ xs) f = cong (_∷_ x) (map-pr1 xs f)




map∃' : {X Y : Set}  → (a : Y) → (f : X → Y) 
 → (xs : List X)
 → a ∈ map f xs → Σ[ x ∈ X ] x ∈ xs × (f x) ≡ a
map∃' a f [] ()
map∃' .(f x) f (x ∷ xs) (here refl) = x , here refl , refl
map∃' a f (x ∷ xs) (there pr) with map∃' a f xs pr 
... | o1 , o2 , o3 = o1 , there o2 , o3


map∃ : {X Y : Set} → (_==_ : Decidable (_≡_ {A = Y})) → (a : Y) → (f : X → Y) 
 → (xs : List X)
 → a ∈ map f xs → Σ[ x ∈ X ] x ∈ xs × (f x) ≡ a
map∃ eq a f [] ()
map∃ eq a f (x ∷ xs) x₁ with eq (f x) a
map∃ eq a f (x ∷ xs) x₁ | yes p rewrite p = x , (here refl) , p
map∃ eq .(f x) f (x ∷ xs) (here refl) | no ¬p with ¬p refl 
... | ()
map∃ eq a f (x ∷ xs) (there x₁) | no ¬p with map∃ eq a f xs x₁ 
map∃ eq a f (x ∷ xs) (there x₁) | no ¬p | proj₁ , o1 , o2  = proj₁ , there o1 , o2


∈-eq-cong : {X : Set} → (x : X) → (xs ys : List X) →  x ∈ xs → xs ≡ ys → x ∈ ys
∈-eq-cong x xs .xs xsin refl = xsin



map-cong2 : {X Y : Set} → (f : Y → X) → (t : X → Y) 
  → (∀ x → t (f x) ≡ x)
  → ∀ x xs → f x ∈ map f xs → x ∈ xs
map-cong2 f t pr x [] ()
map-cong2 f t pr x (x₁ ∷ xs) pr2 with map-cong2' (f x) (f x₁) (map f xs) pr2
  where
     map-cong2' : {X : Set} → (x x1 : X) → (xs : List X) 
        → x ∈ (x1 ∷ xs) → x ≡ x1 ⊎ x ∈ xs
     map-cong2' x1 .x1 xs (here refl) = inj₁ refl
     map-cong2' x1 x2 xs (there inp) = inj₂ inp
map-cong2 f t pr x (x₁ ∷ xs) pr2 | inj₁ x₂ with cong t x₂
... | z rewrite pr x₁ | pr x = subst (λ h → h ∈ (x₁ ∷ xs)) (sym z) (here refl)
map-cong2 f t pr x (x₁ ∷ xs) pr2 | inj₂ y = there (map-cong2 f t pr _ _ y)


map-cong3 : {X Y : Set} → (f : Y → X)
  → (∀ x1 x2 → f x1 ≡ f x2 → x1 ≡ x2)
  → ∀ x xs → f x ∈ map f xs → x ∈ xs
map-cong3 f pr x xs xi with map∃'  (f x) f xs xi 
... | o1 , o2 , o3 rewrite pr o1 x o3 = o2




len-= : {X : Set} → (o1 o2 p1 p2 : List X) 
 → o1 ++ o2 ≡ p1 ++ p2 → length o1 ≡ length p1 → o1 ≡ p1
len-= [] o2 [] p2 pr len = refl
len-= [] o2 (x ∷ p1) p2 pr ()
len-= (x ∷ o1) o2 [] p2 pr ()
len-= (x ∷ o1) o2 (x₁ ∷ p1) p2 pr len rewrite len-= o1 o2 p1 p2 (cong (drop 1) pr) (cong pred len) | cong (λ { (z ∷ zs) → z ; [] → x }) pr = refl

len-=2 : {X : Set} → (o1 o2 p1 p2 : List X) 
 → o1 ++ o2 ≡ p1 ++ p2 → length o1 ≡ length p1 → o2 ≡ p2
len-=2 [] o2 [] p2 prf x = prf
len-=2 [] o2 (x ∷ p1) p2 prf ()
len-=2 (x ∷ o1) o2 [] p2 prf ()
len-=2 (x ∷ o1) o2 (x₁ ∷ p1) p2 prf x₂ = len-=2 o1 o2 p1 p2 (cong (drop 1) prf) (cong pred x₂)


list-⊥ : {X : Set} → (x : X) → (p1 p2 : List X) → p1 ≡ p1 ++ x ∷ p2 → ⊥
list-⊥ x [] p2 ()
list-⊥ x (x₁ ∷ p1) p2 pr = list-⊥ x p1 p2 (cong (drop 1) pr)

list-div : {X : Set} (a b : ℕ) → (xs : List X) 
  → a ≤ b → Σ[ xs' ∈ List X ] take b xs ≡ take a xs ++ xs'
list-div zero zero [] pr = [] , refl
list-div zero (suc b) [] pr = [] , refl
list-div (suc a) zero [] pr = [] , refl
list-div (suc a) (suc b) [] pr = [] , refl
list-div zero zero (x ∷ xs) pr = [] , refl
list-div zero (suc b) (x ∷ xs) pr = x ∷ take b xs , refl
list-div (suc a) zero (x ∷ xs) ()
list-div (suc a) (suc b) (x ∷ xs) (s≤s pr) with list-div a b xs pr 
... | o1 , o2 = o1 , cong (_∷_ x) o2

take-prop : {X : Set} → (o1 o2 : List X) → take (length o1) (o1 ++ o2) ≡ o1
take-prop [] o2 = refl
take-prop (x ∷ o1) o2 = cong (_∷_ x) (take-prop o1 o2)

++-[] : {X : Set} → (o1 : List X) → o1 ++ [] ≡ o1
++-[] [] = refl
++-[] (x ∷ o1) = cong (_∷_ x) (++-[] o1)



map-def : ∀ {a b} {A : Set a} → {B : A → Set b} → (A → Σ[ a ∈ A ] B a) → List A → List (Σ[ a ∈ A ] B a)
map-def f [] = []
map-def f (x ∷ l) = f x ∷ map-def f l

lft : ∀ {a} →  {X : Set a} → (xs : List X) → List (Σ[ x ∈ X ] x ∈ xs)
lft [] = []
lft (x ∷ xs) = (x , (here refl)) ∷ map (λ { (e , p) → e , there p }) (lft xs)


map-in : ∀ {a b} {A : Set a} → {B : Set b} → (as : List A) → (Σ[ a ∈ A ] a ∈ as → B) → List B
map-in xs f = map f (lft xs)


mapmap : ∀{a b c} {X : Set a}{Y : Set b}{Z : Set c} → (g : Y → Z) → (f : X → Y)
  → (xs : List X)
  → map g (map f xs) ≡ map (λ x → g (f x)) xs
mapmap f g [] = refl
mapmap f g (x ∷ xs) = cong (_∷_ _) (mapmap f g xs)

map-in-pr : ∀{a b} → {A : Set a} → {B : Set b} → (as : List A) → (f : Σ[ a ∈ A ] a ∈ as → B) → ∀ a → a ∈ as → Σ[ p ∈ (a ∈ as) ] (f (a , p)) ∈ (map-in as f)
map-in-pr [] f a₁ ()
map-in-pr (x ∷ as) f .x (here refl) = (here refl , here refl)
map-in-pr (x ∷ as) f x₁ (there ain) with map-in-pr as (λ a → f ((proj₁ a) , (there (proj₂ a)))) x₁ ain 
... | ass , ps = there ass , there (subst (λ x → f (x₁ , there ass) ∈ x) (sym (mapmap f (λ ep → proj₁ ep , there (proj₂ ep)) (lft as))) ps)


map-def-pr : {l1 l2 : Level}{X : Set l1}{Y : X → Set l2} → (l : List X) 
  → (f : (x : X) → Y x)→ map proj₁ (map-def (λ el1 → el1 , f el1) l) ≡ l
map-def-pr [] f = refl
map-def-pr (x ∷ l) f = cong (_∷_ x) (map-def-pr l f)



NoDup+Dup : {X : Set} → (xs : List X) → Set
NoDup+Dup {X} xs = NoDup xs ⊎ (Σ[ ys ∈ List X ] 
                               Σ[ zs ∈ List X ] 
                               Σ[ x ∈ X ] xs ≡ ys ++ zs × x ∈ ys × x ∈ zs)



count : {X : Set} → DecEq X → X → List X → ℕ
count d x [] = 0
count d x₁ (x ∷ xs)  with d x x₁ 
... | yes _ = 1 + count d x₁ xs
... | no _  = count d x₁ xs


countHom : {X : Set} → (eq : DecEq X) → (xs ys : List X) → (x : X) 
  →  count eq x (xs ++ ys) ≡ count eq x xs + count eq x ys
countHom d [] ys x = refl
countHom d (x ∷ xs) ys x₁ with d x x₁
countHom d (x ∷ xs) ys x₁ | yes p rewrite countHom d xs ys x₁ = refl
countHom d (x ∷ xs) ys x₁ | no ¬p rewrite countHom d xs ys x₁ = refl 


count∉ : {X : Set} → (eq : DecEq X) → (xs : List X) → (x : X) 
   → ¬ x ∈ xs → count eq x xs ≡ 0
count∉ d [] x xnin = refl
count∉ d (x ∷ xs) x₁ xnin with d x x₁ 
count∉ d (x ∷ xs) .x xnin | yes refl with xnin (here refl)
... | ()
count∉ d (x ∷ xs) x₁ xnin | no _ = count∉ d xs x₁ (λ xin → xnin (there xin)) 


count∈ : {X : Set} → (eq : DecEq X) → (xs : List X) → (x : X) 
  → x ∈ xs → Σ[ n ∈ ℕ ] count eq x xs ≡ suc n
count∈ d (.x ∷ xs) x (here refl) with d x x 
... | yes p = count d x xs , refl
... | no p with p refl 
... | ()
count∈ d (y ∷ xs) x (there xin) with d y x 
... | yes p = count d x xs , refl
... | no p = count∈ d xs x xin


countNoDup : {X : Set} → (d : Decidable (_≡_ {A = X})) → (xs : List X) → (x : X) 
 → NoDup xs → x ∈ xs → count d x xs ≡ 1
countNoDup d xs x nd xin  with nd x  xin 
... | o1 , o2 , o3 , o4 , o5 rewrite o3 | countHom d o1 (x ∷ o2) x with d x x
... | yes p rewrite count∉ d  o1 x  o4 | count∉ d  o2 x  o5 = refl
... | no p with p refl 
... | ()

notNoDup : {X : Set} → {d : DecEq X} → (xs : List X) 
  → (Σ[ ys ∈ List X ] 
      Σ[ zs ∈ List X ] 
      Σ[ x ∈ X ] xs ≡ ys ++ zs × (x ∈ ys) × (x ∈ zs)) 
  → ¬ NoDup xs
notNoDup {_} {d} xs (proj₁ , proj₂ , proj₃ , proj₄ , proj₅ , proj₆) nd 
  with nd proj₃ (subst (λ z → proj₃ ∈ z) (sym proj₄) (++⁺ʳ proj₁ proj₆)) 
... | o1 , o2 , o3 , o4 , o5  rewrite proj₄ with cong (count d proj₃) o3 
... | po rewrite countHom d proj₁ proj₂ proj₃ | countHom d o1 (proj₃ ∷ o2) proj₃  with d proj₃ proj₃ 
... | no p = p refl
... | yes p rewrite count∉ d o1 proj₃ o4 | count∉ d o2 proj₃ o5 with 
 count∈ d proj₁ proj₃ proj₅ | count∈ d proj₂ proj₃ proj₆
... | z , zp | w , wp  rewrite zp | wp | +-comm z (suc w) with po 
... | ()


nodup+dup : {X : Set} → DecEq X → (xs : List X) → NoDup+Dup xs
nodup+dup dec [] = inj₁ (λ { x () })
nodup+dup dec (x ∷ xs)  with nodup+dup dec xs  
nodup+dup dec (x₁ ∷ xs) | inj₁ x with (eq2in dec) x₁ xs 
nodup+dup dec (x₁ ∷ xs) | inj₁ x | yes p with ∃-split x₁ xs p 
... | o1 , o2 , o3 = inj₂ (x₁ ∷ o1 , x₁ ∷ o2 , x₁ , cong (_∷_ x₁) o3 , here refl , here refl) 
nodup+dup {X} dec (x₁ ∷ xs) | inj₁ x | no ¬p = inj₁ (h xs x₁ ¬p x)
  where
    h : (xs1 : List X) → (x₁ : X) → (¬p  : ¬ x₁ ∈ xs1) 
      → NoDup xs1
      → (x₂ : X)
      → x₂ ∈ (x₁ ∷ xs1) →
      Σ (List X)
      (λ ys →
         Σ (List X)
         (λ zs →
            Σ (x₁ ∷ xs1 ≡ ys ++ x₂ ∷ zs)
            (λ x₃ → Σ (x₂ ∈ ys → ⊥) (λ x₄ → x₂ ∈ zs → ⊥))))
    h xs₁ x1 ¬p nd x xin with dec x x1
    h xs₁ x1 ¬p₁ nd .x1 (here refl) | yes refl = [] , xs₁ , refl , (λ { () }) , ¬p₁
    h xs₁ x1 ¬p₁ nd .x1 (there xin) | yes refl with ¬p₁ xin 
    ... | ()
    h xs₁ x1 ¬p₂ nd .x1 (here refl) | no ¬p₁ with ¬p₁ refl 
    ... | ()

    h xs₁ x1 ¬p₂ nd x₂ (there xin) | no ¬p₁ with nd x₂ xin 
    ... | q1 , q2 , q3 , q4 , q5 = x1 ∷ q1 , q2 , cong (_∷_ x1) q3 , blh x₂ x1 q1 ¬p₁ q4 , q5
      where
        blh : {A : Set} → (a b : A) → (cs : List A) →  (a ≡ b → ⊥) → (a ∈ cs → ⊥) → a ∈ (b ∷ cs) → ⊥
        blh a .a cs pr1 pr2 (here refl) = pr1 refl
        blh a b cs pr1 pr2 (there pr3) = pr2 pr3
nodup+dup dec (x₁ ∷ xs)  | inj₂ (ys , zs , e , p , q1 , q2) = inj₂ (x₁ ∷ ys , zs , e , cong (_∷_ x₁) p , there q1 , q2) 



nodupDec2 : {X : Set} → DecEq X → (xs : List X) → Dec (NoDupInd xs)
nodupDec2 eq [] = yes []
nodupDec2 eq (x ∷ xs) with nodupDec2 eq xs 
nodupDec2 eq (x ∷ xs) | yes p with eq2in eq x xs 
nodupDec2 eq (x ∷ xs) | yes p₁ | yes p = no (λ { (x₁ ∷ nd) → (All¬⇒¬Any x₁ p) })
nodupDec2 eq (x ∷ xs) | yes p | no ¬p = yes (¬Any⇒All¬ xs ¬p ∷ p)
nodupDec2 eq (x ∷ xs) | no ¬p = no (λ { (x₁ ∷ nd) → ¬p nd } )

nodupDec : {X : Set} → DecEq X → (xs : List X) → Dec (NoDup xs)
nodupDec d xs with nodup+dup d xs
nodupDec d xs | inj₁ x = yes x
nodupDec d xs | inj₂ y = no (notNoDup {_} {d} xs y)
