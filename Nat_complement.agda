-- Time-stamp: <2020-10-15 09:59:10 pierre>
{--------------------------------------------------------------------
   © Pierre Lescanne                          Agda version 2.6.1.1
 
                            Nat_complement
 --------------------------------------------------------------------}
module Nat_complement where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_;refl; cong; sym)
open import Data.Maybe
open import Data.Bool using (Bool; if_then_else_; _∧_) renaming (false to °; true to ¹;not to ¬_)
open import Data.List using (List; _++_;[_];_∷ʳ_) renaming ([] to ε;_∷_ to _::_)
open import Data.Vec using (Vec;[];_∷_;zip;_⊛_;tail;head) renaming (map to mapV)
open import Data.Product using (_×_;_,_;proj₁;proj₂)
open import Data.Sum using (_⊎_;[_,_]′;inj₁;inj₂)

-- ===================================================
-- ========== a limit for the normalisation ==========
-- ===================================================
limit = 5

-- ==================== Comparisons with booleans  ====================
_<_ : ℕ → ℕ → Bool
0 < (suc _) = ¹
suc n < suc m = n < m
_ < _ = °

_=ℕ=_ : ℕ → ℕ → Bool
0 =ℕ= 0 = ¹
suc n₁ =ℕ= suc n₂ = n₁ =ℕ= n₂
_ =ℕ= _ = °

-- =================== Relations ===============================
-- Leibniz equality 
_≐_ : {A : Set} → A → A → Set₁
x ≐ y = (P : _ → Set) → P x → P y

-- Properties
≐-refl : {A : Set}{x : A} → x ≐ x
≐-refl P Px = Px

≐-sym : {A : Set}{x y : A} → x ≐ y → y ≐ x
≐-sym {x = x} {y} h P Py = h (λ z → P z → P x) (λ Px → Px) Py

≐-trans : {A : Set}{x y z : A} → x ≐ y → y ≐ z → x ≐ z
≐-trans h₁ h₂ P Px = h₂ P (h₁ P Px)

≐-subst : {A : Set}(P : A → Set){x y : A} → x ≐ y → P x → P y
≐-subst P h = h P

--- Relations on ℕ ---
--- ≡ ---
SM≡ : (m n : ℕ) → Maybe (m ≡ n) → Maybe ((suc m) ≡ (suc n))
SM≡ m .m (just refl) = just refl
SM≡ m n nothing = nothing

_≡?_ : (m n : ℕ) → Maybe (m ≡ n)
zero ≡? zero = just refl
zero ≡? suc n = nothing
suc m ≡? zero = nothing
suc m ≡? suc n = SM≡ m n (m ≡? n) 
-----------
---- ≺ ----
-----------
data _≺_ : ℕ → ℕ → Set where
  z≺s : {n : ℕ} → zero ≺ suc n
  s≺s : {n m : ℕ} → n ≺ m → suc n ≺ suc m

-- inversion of s≺s
inv-s≺s : {n m : ℕ} → suc n ≺ suc m → n ≺ m
inv-s≺s (s≺s e) = e

-- fact 1
≺suc : {i n : ℕ} → (i ≺ n) → i ≺ (suc n)
≺suc z≺s = z≺s
≺suc (s≺s p) = s≺s (≺suc p)

-- fatc 2
≺→0≺ : {i n : ℕ} → (i ≺ n) → 0 ≺ n
≺→0≺ z≺s = z≺s
≺→0≺ (s≺s p) = z≺s

-- transitivity
trans≺ : {n₁ n₂ n₃ : ℕ} → n₁ ≺ n₂ → n₂ ≺ n₃ → n₁ ≺ n₃
trans≺ z≺s (s≺s _) = z≺s 
trans≺ (s≺s p) (s≺s p')= s≺s (trans≺ p p')

-- Maybe s≺s 
S≺S : {n m : ℕ} → Maybe (n ≺ m) → Maybe (suc n ≺ suc m)
S≺S nothing = nothing
S≺S (just p) = just (s≺s p)

-----------
---- ≼ ----
-----------
data _≼_ : ℕ → ℕ → Set where
  z≼n : {n : ℕ} → 0 ≼ n
  s≼s : {m n : ℕ} → m ≼ n → suc m ≼ suc n

s≼s-inv : {m n : ℕ} → suc m ≼ suc n → m ≼ n
s≼s-inv (s≼s p) = p

≺→≼ : {m n : ℕ} → m ≺ n → m ≼ n
≺→≼ z≺s = z≼n
≺→≼ (s≺s p) = s≼s (≺→≼ p)

_≼?_ : (m n : ℕ) → Maybe (m ≼ n)
0 ≼? _ = just z≼n
suc _ ≼? 0 = nothing
suc m ≼? suc n with m ≼? n
...| nothing = nothing
...| just p = just (s≼s p)

-- reflexivity
refl≼ : {n : ℕ} → n ≼ n
refl≼ {0} = z≼n
refl≼ {suc n} = s≼s refl≼

-- transitivity
trans≼ : {n₁ n₂ n₃ : ℕ} → n₁ ≼ n₂ → n₂ ≼ n₃ → n₁ ≼ n₃
trans≼ z≼n _ = z≼n
trans≼ (s≼s p) (s≼s p') = s≼s (trans≼ p p')

-- totalness of ≼
total≼ : (m n : ℕ) → m ≼ n ⊎ n ≼ m
total≼ 0 _ = inj₁ z≼n
total≼ (suc n) 0 = inj₂ z≼n
total≼ (suc m) (suc n) = [ f≼ , f≽ ]′ (total≼ m n) where
  f≼ : m ≼ n →  suc m ≼ suc n ⊎ suc n ≼ suc m
  f≼ p = inj₁ (s≼s p)

  f≽ : n ≼ m →  suc m ≼ suc n ⊎ suc n  ≼ suc m
  f≽ p = inj₂ (s≼s p)

--
s≼→0≺ : {n m : ℕ} → suc n ≼ m → 0 ≺ m
s≼→0≺ (s≼s p) = z≺s

-----------
---- ≠ ----
-----------

data _≠_ : ℕ → ℕ → Set where
  z≠s : {n : ℕ} → zero ≠ suc n
  s≠z : {n : ℕ} → suc n ≠ zero
  s≠s : {n m : ℕ} → n ≠ m → suc n ≠ suc m
  
-- given two naturals n and m, n ≺? m is maybe a proof of n ≺ m
_≺?_ : (n m : ℕ) → Maybe (n ≺ m)
_ ≺? 0 = nothing
0 ≺? (suc n) = just z≺s
(suc n) ≺? (suc m) = S≺S (n ≺? m)

S≠S : {n m : ℕ} → Maybe (n ≠ m) → Maybe (suc n ≠ suc m)
S≠S nothing = nothing
S≠S (just p) = just (s≠s p)

-- given two naturals n and m, n ≠? m is maybe a proof of n ≠ m
_≠?_ : (n m : ℕ) → Maybe (n ≠ m)
0 ≠? 0 = nothing
0 ≠? (suc _) = just z≠s
(suc _) ≠? 0 = just s≠z
(suc n) ≠? (suc m) = S≠S (n ≠? m)

-----------
--- _=̂_ ---
-----------

data _=̂_ : ℕ → ℕ → Set where   -- recursive equality over ℕ
  z=̂z : zero =̂ zero
  s=̂s : {n m : ℕ} → n =̂ m → suc n =̂ suc m

-- recursive equality implies Leibniz equality
=̂→≐ : {n m : ℕ} → n =̂ m → n ≐ m
=̂→≐ z=̂z = ≐-refl
=̂→≐ (s=̂s p) = λ P → =̂→≐ p (λ z → P (suc z))

-- given two naturals n and m, n =̂? m is maybe a proof of n =̂ m
_=̂?_ : (n m : ℕ) → Maybe (n =̂ m)
0 =̂? 0 = just z=̂z
0 =̂? (suc _) = nothing
(suc _) =̂? 0 = nothing
(suc n) =̂? (suc m) with (n =̂? m)
(suc n) =̂? (suc m) | nothing = nothing
(suc n) =̂? (suc m) | just p = just (s=̂s p )

-- reflexivity of =̂
ref=̂ : (n : ℕ) → n =̂ n
ref=̂ 0 = z=̂z
ref=̂ (suc n) = s=̂s (ref=̂ n)

-- symmetry of =̂
sym=̂ : {n m : ℕ} → n =̂ m → m =̂ n
sym=̂ z=̂z =  z=̂z
sym=̂ (s=̂s p) = s=̂s (sym=̂ p)

-- transitivity of =̂
trans=̂ : {n m p : ℕ} → n =̂ m → m =̂ p → n =̂ p
trans=̂  z=̂z z=̂z = z=̂z
trans=̂  (s=̂s p₁) (s=̂s p₂) = s=̂s (trans=̂ p₁ p₂)

-- =̂ implies ≼
=̂→≼ : {m n : ℕ} → m =̂ n → m ≼ n
=̂→≼ z=̂z = z≼n
=̂→≼ (s=̂s p) = s≼s (=̂→≼ p)

-- pseudo-transitivity of ≼
trans2≼ : {n₁ n₂ n₃ : ℕ} → n₁ ≼ n₂ → n₂ =̂ n₃ → n₁ ≼ n₃
trans2≼ z≼n _ = z≼n
trans2≼ (s≼s p) (s=̂s p') = s≼s (trans2≼ p p')

-- pseudo-transitivity of ≺
=̂≺→≺ : {i k n : ℕ} → i =̂ k → i ≺ n → k ≺ n
=̂≺→≺ z=̂z z≺s = z≺s
=̂≺→≺ (s=̂s p) (s≺s p') = s≺s (=̂≺→≺ p p')

-- 2nd pseudo-transitivity of ≺
≺≼→≺ : {i k n : ℕ} → i ≺ k → k ≼ n → i ≺ n
≺≼→≺ {0} {suc k} {suc n} _ _  = z≺s
≺≼→≺ (s≺s p) (s≼s p') = s≺s (≺≼→≺ p p')

-- 3rd pseudo-transitivity of ≺
≺=̂→≺ : {i k n : ℕ} → i ≺ k → k =̂ n → i ≺ n
≺=̂→≺ {0} {suc k} {suc n} z≺s ref=̂ = z≺s
≺=̂→≺ (s≺s p) (s=̂s p') = s≺s (≺=̂→≺ p p')

-- totalness of ≺
total≺ : (n m : ℕ) → n ≺ m ⊎ n =̂ m ⊎ m ≺ n
total≺ 0 0 = inj₂ (inj₁ z=̂z)
total≺ 0 (suc m) = inj₁ z≺s
total≺ (suc n) 0 = inj₂ (inj₂ z≺s)
total≺ (suc n) (suc m) = [ f≺ , [ f=̂ , f≻ ]′ ]′ (total≺ n m) where
  f≺ : n ≺ m →  suc n ≺ suc m ⊎ suc n =̂ suc m ⊎ suc m ≺ suc n
  f≺ p = inj₁ (s≺s p)

  f=̂ : n =̂ m →  suc n ≺ suc m ⊎ suc n =̂ suc m ⊎ suc m ≺ suc n
  f=̂ p = inj₂ (inj₁ (s=̂s p))

  f≻ : m ≺ n →  suc n ≺ suc m ⊎ suc n =̂ suc m ⊎ suc m ≺ suc n
  f≻ p = inj₂ (inj₂ (s≺s p))

-- ==================== on Lists ====================
data _isIn_ : {A : Set} → A → List A → Set where
  in₁ : {A : Set} → {a : A} → {l : List A} → a isIn (a :: l)
  in₂ : {A : Set} → {a₁ a₂ : A} → {l : List A} → a₁ isIn l → a₁ isIn (a₂ :: l)

-- two different lists
data _≠α_ : List Bool → List Bool → Set where
  ε≠∷ : (b : Bool) → (α : List Bool) → ε ≠α (b :: α) 
  ∷≠ε : (b : Bool) → (α : List Bool) → (b :: α) ≠α ε
  0∷≠1∷ : (α β : List Bool) → (° :: α) ≠α (¹ :: β)
  1∷≠0∷ : (α β : List Bool) → (¹ :: α) ≠α (° :: β)
  0∷≠0∷ : (α β : List Bool) → α ≠α β → (° :: α) ≠α (° :: β)
  1∷≠1∷ : (α β : List Bool) → α ≠α β → (¹ :: α) ≠α (¹ :: β)

data _≠iα_ : ℕ × List Bool → ℕ × List Bool → Set where
  N≠ : (n₁ n₂ : ℕ) → (α β : List Bool) → n₁ ≠ n₂ → (n₁ , α) ≠iα (n₂ , β)
  L≠ : (i j : ℕ) → (α β : List Bool) → α ≠α β → (i , α) ≠iα (j , β)

data _=ℕ_ : List ℕ → List ℕ → Set where
  ε=ℕε : ε =ℕ ε
  ∷=ℕ∷ : {x₁ x₂ : ℕ} → {l₁ l₂ : List ℕ} → x₁ =̂ x₂ → l₁ =ℕ l₂ → (x₁ :: l₁) =ℕ (x₂ :: l₂)

_=ℕ?_ : (l₁ l₂ : List ℕ) → Maybe (l₁ =ℕ l₂)
ε =ℕ? ε = just (ε=ℕε)
ε =ℕ? (_ :: _) = nothing
(_ :: _) =ℕ? ε = nothing
(x1 :: l1) =ℕ? (x2 :: l2) = case (x1 =̂? x2) (l1 =ℕ? l2)
    where case : Maybe (x1 =̂ x2) → Maybe (l1 =ℕ l2) → Maybe ((x1 :: l1) =ℕ (x2 :: l2))
          case  (just p) (just p') = just (∷=ℕ∷ p p')
          case nothing _ = nothing
          case _ nothing = nothing

-- ============================== Finite sets ==============================
-- the family of numbers smaller than a given natural number.
data Fin : ℕ -> Set where
  fzero : {n : ℕ} -> Fin (suc n)
  fsuc : {n : ℕ} -> Fin n -> Fin (suc n)

-- ============================== On Vectors ==============================
-- Boolean equality of vectors
_=v=_ : {n : ℕ} → Vec ℕ n → Vec ℕ n → Bool
[] =v= [] = ¹
(n₁ ∷ v₁) =v= (n₂ ∷ v₂) = (n₁ =ℕ= n₂) ∧ (v₁ =v= v₂)
