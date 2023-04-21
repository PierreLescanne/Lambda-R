-- Time-stamp: <2023-04-21 10:23:23 pierre>
{--------------------------------------------------------------------
   © Pierre Lescanne                          Agda version 2.6.1
 
                                 LIST
 --------------------------------------------------------------------}

module LIST where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_;refl; cong; sym)
open import Data.Bool using (Bool; if_then_else_) renaming (not to ¬_;false to °;true to ¹)
open import Data.Nat using (ℕ; zero; suc)
open import Nat_complement
open import Data.Maybe using (Maybe; nothing; just)
open import Data.List using (List; map; _++_) renaming (_∷_ to _:l:_; [] to ε)
open import Data.Sum using (_⊎_;[_,_]′;inj₁;inj₂)
open import Data.Product using (_×_;_,_;proj₁;proj₂)
open import Data.Unit using (⊤;tt)

-- ====================
--   Sequence
-- ====================

-- a Sequence is a non empty list
data Sequence : Set where
  [_]ˢ : ℕ → Sequence 
  _∷_ : ℕ → Sequence → Sequence

-- on Sequence, hd is always defined, i.e., is total
hd : Sequence → ℕ
hd [ n ]ˢ = n
hd (n ∷ _) = n

map1ˢ : Sequence → Sequence
map1ˢ [ n ]ˢ = [ suc n ]ˢ
map1ˢ (n ∷ s) = suc n ∷ map1ˢ s

lengthˢ : Sequence → ℕ
lengthˢ [ _ ]ˢ = 1
lengthˢ (_ ∷ s) = suc (lengthˢ s)

--------------------
-- predicate sorted
--------------------
data sorted : Sequence → Set where
  sorted1 : {n : ℕ} → sorted [ n ]ˢ
  sorted∷ : {n : ℕ} → {s : Sequence} → n ≼ (hd s) → sorted s → sorted (n ∷ s)

-- a sequence with two elements is sorted, if  the first is less than or equal to the second
sorted2≼ : {n₁ n₂ : ℕ} → n₁ ≼ n₂ → sorted (n₁ ∷ [ n₂ ]ˢ)
sorted2≼ p = sorted∷ p sorted1 

sorted2≼' : {n₁ n₂ : ℕ} → sorted (n₁ ∷ [ n₂ ]ˢ) → n₁ ≼ n₂ 
sorted2≼' (sorted∷ p sorted1)  = p

-- sorted (n ∷ s) implies n ≼ (hd s)
sorted-inv₁ : {n : ℕ} → {s : Sequence} → sorted (n ∷ s) → n ≼ (hd s)
sorted-inv₁ (sorted∷ p _) = p

-- sorted (n ∷ s) implies sorted s
sorted-inv₂ : {n : ℕ} → {s : Sequence} → sorted (n ∷ s) → sorted s
sorted-inv₂ (sorted∷ _ p) = p

----------------------
-- down  the indices
----------------------

-- all the indices of the Sequence are strictly positive
data Seq≻0 : Sequence → Set where
  Seq≻0[] : {k : ℕ} → Seq≻0 [ suc k ]ˢ
  Seq≻0∷ : {k : ℕ} → {s : Sequence} → Seq≻0 s → Seq≻0 (suc k ∷ s)

Seq≻0? : (s : Sequence) → Maybe (Seq≻0 s)
Seq≻0? [ suc k ]ˢ = just Seq≻0[]
Seq≻0? (suc k ∷ s) with Seq≻0? s
... | nothing = nothing
... | just p = just (Seq≻0∷ p)
Seq≻0? _ = nothing

-- down the indices
⇓ : {s : Sequence} → Seq≻0 s → Sequence
⇓ (Seq≻0[] {k}) = [ k ]ˢ
⇓ (Seq≻0∷ {k} {s} p) with ⇓ p
⇓ (Seq≻0∷ {k} {s} p) | s' = k ∷ s'

-- ⇓ preserves sortedness
≼hd⇓ : {k : ℕ} → {s : Sequence} → (p : Seq≻0 s) → suc k ≼ hd s → k ≼ hd (⇓ p)
≼hd⇓ Seq≻0[] (s≼s p) = p
≼hd⇓ (Seq≻0∷ _) (s≼s p) = p

⇓-sorted : {s : Sequence} → (p : Seq≻0 s) → sorted s → sorted (⇓ p)
⇓-sorted Seq≻0[] p = sorted1
⇓-sorted (Seq≻0∷ p₁) (sorted∷ p p') = sorted∷ (≼hd⇓ p₁ p) (⇓-sorted p₁ p')

------------------------------
-- an instance of η-conversion
------------------------------
postulate
  η-hd : {n : ℕ} → {s : Sequence} → n =̂ hd (n ∷ s)

------------------------
-- Induction on Sequence
------------------------
postulate
  Sequence-induction : (P : Sequence → Set) →
    ((n : ℕ) → P [ n ]ˢ) → ((n : ℕ) → (s : Sequence) → P s → P (n ∷ s)) →
    --------------------------------------------------------------------
               (s : Sequence) → P s

----------------------------------
-- Induction on pairs of Sequences
----------------------------------
postulate
  pair-Sequence-induction : (P : Sequence → Sequence → Set) →
    ((n : ℕ) → (s : Sequence) → P [ n ]ˢ s) →
    ((n m : ℕ) → (s : Sequence) → P (m ∷ s) [ n ]ˢ) →
    ((n₁ n₂ : ℕ) → (s₁ s₂ : Sequence) → P s₁ (n₂ ∷ s₂) → P (n₁ ∷ s₁) s₂ → P (n₁ ∷ s₁) (n₂ ∷ s₂)) → 
    -----------------------------------------------------------------------------------------------
             (s₁ s₂ : Sequence) → P s₁ s₂

------------------------------------------
-- insert an element in a sorted sequence
------------------------------------------
insert : ℕ → Sequence → Sequence
insert n [ m ]ˢ with total≼ n m
... | inj₁ _ = n ∷ [ m ]ˢ -- n ≼ m
... | inj₂ _ = m ∷ [ n ]ˢ -- m ≼ n
insert n (m ∷ s) with total≼ n m
... | inj₁ _ = n ∷ (m ∷ s) -- n ≼ m
... | inj₂ _ = m ∷ (insert n s) -- m ≼ n

-- insert preserves sortedness

hd-lemma : {i n : ℕ} → {s : Sequence} → i ≼ n → i ≼ hd s → i ≼ hd (insert n s)
hd-lemma {i} {n} {[ k ]ˢ} p p' with total≼ n k
... | inj₁ p≼ = p
... | inj₂ p≽ = p'
hd-lemma {i} {n} {k ∷ s} p p' with total≼ n k
... | inj₁ p≼ = p
... | inj₂ p≽ = p'

InsSort[] : (n : ℕ) → sorted [ n ]ˢ → (k : ℕ ) → sorted (insert k [ n ]ˢ)
InsSort[] n sorted1 k with total≼ k n
... | inj₁ p≼ = sorted∷ p≼ sorted1
... | inj₂ p≽ = sorted∷ p≽ sorted1

InsSort∷ : (n : ℕ) → (s : Sequence) → (sorted s → ∀ k → sorted (insert k s)) → sorted (n ∷ s) → ∀ k → sorted (insert k (n ∷ s))
InsSort∷ k s p (sorted∷ pᵢₙ pₛₒᵣ) n with total≼ n k
... | inj₁ p≼ = sorted∷ p≼ (sorted∷ pᵢₙ pₛₒᵣ)
... | inj₂ p≽ = sorted∷ (hd-lemma {k} {n} {s} p≽ pᵢₙ)(p pₛₒᵣ n)

InsSortInd : ((n : ℕ) → sorted [ n ]ˢ → ∀ k → sorted (insert k [ n ]ˢ)) →
          ((n : ℕ) → (s : Sequence) → (sorted s → ∀ k → sorted (insert k s)) → sorted (n ∷ s) → ∀ k → sorted (insert k (n ∷ s))) →
          (∀ s → sorted s → ∀ k → sorted (insert k s))
InsSortInd = Sequence-induction (λ z → (x : sorted z) (x₁ : ℕ) → sorted (insert x₁ z))

InsSort : ∀ s → sorted s → ∀ n → sorted (insert n s)
InsSort = InsSortInd InsSort[] InsSort∷

-- A sorted Sequence with a positive head has all its elements positive
sorted→≻0 : {s : Sequence} → 0 ≺ hd s → sorted s → Seq≻0 s
sorted→≻0 p0≺ sorted1 = lemma p0≺ where
  lemma : {k : ℕ} → 0 ≺ k → Seq≻0 [ k ]ˢ
  lemma z≺s = Seq≻0[]
sorted→≻0 p0≺ (sorted∷ p≺ pₛ) = lemma' p0≺ (sorted→≻0 (≺≼→≺ p0≺ p≺) pₛ) where
  lemma' : {k : ℕ} → {s : Sequence} → 0 ≺ k → Seq≻0 s → Seq≻0 (k ∷ s)
  lemma' z≺s p = Seq≻0∷ p

----------------------
-- merge two sequences
----------------------
_‡ˢ_ : Sequence → Sequence → Sequence
[ n ]ˢ ‡ˢ s = insert n s
(n₁ ∷ s₁) ‡ˢ s = insert n₁ (s₁ ‡ˢ s)

-- =-=-=-=-=-=-=-=-=-=-=-=-
--  ‡ˢ preserves sortedness
-- =-=-=-=-=-=-=-=-=-=-=-=-
‡ˢ-sorted : (s₁ s₂ : Sequence) → sorted s₁ → sorted s₂ → sorted (s₁ ‡ˢ s₂)
‡ˢ-sorted [ n₁ ]ˢ s₂ sorted1 p =  InsSort s₂ p n₁
‡ˢ-sorted (n₁ ∷ s₁) s₂ p₁ p₂ = InsSort (s₁ ‡ˢ s₂) (‡ˢ-sorted s₁ s₂ (sorted-inv₂ p₁) p₂) n₁

-- =============
-- LIST as a sum
-- =============

LIST : Set
LIST = ⊤ ⊎ Sequence

[] : LIST
[] = inj₁ tt

[_] : ℕ → LIST
[ n ] = inj₂ [ n ]ˢ

_::_ : ℕ → LIST → LIST
n :: (inj₂ s) = inj₂ (n ∷ s)
n :: [] = [ n ]

map1 : LIST → LIST
map1 (inj₁ _) = []
map1 (inj₂ s) = inj₂ (map1ˢ s)

length : LIST → ℕ
length (inj₁ _) = 0
length (inj₂ s) = lengthˢ s

data sortedL : LIST → Set where
  sortedL⊤ : sortedL (inj₁ tt)
  sortedLS : {s : Sequence} → sorted s → sortedL (inj₂ s)

--------------------
-- merge two lists
--------------------

_‡_ : LIST → LIST → LIST
(inj₁ tt) ‡ ℓ = ℓ
(inj₂ s) ‡ (inj₁ tt) = inj₂ s
(inj₂ s₁) ‡ (inj₂ s₂) = inj₂ (s₁ ‡ˢ s₂)

-- preservation of sortedness by ‡
‡-sorted : (ℓ₁ ℓ₂ : LIST) → sortedL ℓ₁ → sortedL ℓ₂ → sortedL (ℓ₁ ‡ ℓ₂)
‡-sorted (inj₁ tt) _ _ p₂ = p₂
‡-sorted (inj₂ _) (inj₁ tt) p₁ _ = p₁
‡-sorted (inj₂ s₁) (inj₂ s₂) (sortedLS p₁) (sortedLS p₂) = sortedLS ((‡ˢ-sorted s₁ s₂) p₁ p₂)

-- all the indices of the LIST are strictly positive except the first one
data _∈-0::LIST-ℕ⁺ : LIST → Set where
  [0]≻0 : (inj₂ [ 0 ]ˢ) ∈-0::LIST-ℕ⁺
  0∷≻0 : {s : Sequence} → Seq≻0 s → (inj₂ (0 ∷ s)) ∈-0::LIST-ℕ⁺

∈-0::LIST-ℕ⁺? : (ℓ : LIST) → Maybe (ℓ ∈-0::LIST-ℕ⁺)
∈-0::LIST-ℕ⁺? (inj₂ [ 0 ]ˢ) = just [0]≻0 
∈-0::LIST-ℕ⁺? (inj₂ (0 ∷ s)) with Seq≻0? s
... | nothing = nothing
... | just p = just (0∷≻0 p)
∈-0::LIST-ℕ⁺? _ = nothing

-- down the indices
↓ : {ℓ : LIST} → ℓ ∈-0::LIST-ℕ⁺ → LIST
↓ [0]≻0 = []
↓ (0∷≻0 p) = inj₂ (⇓ p)

-- ↓ preserves sortedness
↓-sorted : {ℓ : LIST} → sortedL ℓ → (p : ℓ ∈-0::LIST-ℕ⁺) → sortedL (↓ p)
↓-sorted _ [0]≻0  = sortedL⊤
↓-sorted (sortedLS (sorted∷ _ pₛₒᵣ)) (0∷≻0 p) = sortedLS (⇓-sorted p pₛₒᵣ)

