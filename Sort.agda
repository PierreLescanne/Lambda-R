-- Time-stamp: <2020-07-04 10:09:51 pierre>
{--------------------------------------------------------------------
© Pierre Lescanne Pierre.Lescanne@ens-lyon.fr      Agda version 2.6.1
 
                                 Sort
 --------------------------------------------------------------------}

module Sort where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_;_,_;proj₁;proj₂)
open import Data.Sum using (_⊎_;[_,_]′;inj₁;inj₂)
open import Data.Unit using (⊤;tt)
open import LIST

postulate
  ℕ-induction :
    (P : ℕ → Set) → (P 0) → (∀ n → (P n) → P (suc n)) → ∀ n → P n

-------------------------
-- a genering sorting algorithm
-------------------------
sort : ℕ → (LIST → (LIST × LIST)) → LIST → LIST
sort 0 _ _ = inj₁ tt
sort (suc n) _ (inj₁ tt) = inj₁ tt
sort (suc n) _ (inj₂ [ k ]ˢ) = inj₂ [ k ]ˢ 
sort (suc n) split (inj₂ (k ∷ s)) with split (inj₂ (k ∷ s))
...| ℓ₁ , ℓ₂ = sort n split ℓ₁ ‡ sort n split ℓ₂

--------------------------------------------
-- Correction : the result of sort is sorted
--------------------------------------------
-- a lemma
sort-sorts-suc : (split : LIST → (LIST × LIST)) → (n : ℕ) → ((ℓ : LIST) → sortedL (sort n split ℓ)) →
    (ℓ : LIST) → sortedL (sort (suc n) split ℓ)
sort-sorts-suc split _ _ (inj₁ tt) = sortedL⊤
sort-sorts-suc split _ _ (inj₂ [ k ]ˢ) = sortedLS sorted1
sort-sorts-suc split n φ (inj₂ (k ∷ s)) with split (inj₂ (k ∷ s))
...| ℓ₁ , ℓ₂ = ‡-sorted (sort n split ℓ₁)  (sort n split ℓ₂) (φ ℓ₁) (φ ℓ₂) 

-- the theorem
sort-sorts : (split : LIST → (LIST × LIST)) → (n : ℕ) → (ℓ : LIST) → sortedL (sort n split ℓ)
sort-sorts split = ℕ-induction (λ n → (ℓ : LIST) → sortedL (sort n split ℓ)) (λ ℓ → sortedL⊤)
                               (sort-sorts-suc split)

-- =-=-=-=-=-=-=-=-=-=-
-- Examples
-- =-=-=-=-=-=-=-=-=-=-

----------------------
-- insertion sort
----------------------

insertion-split : LIST → (LIST × LIST)
insertion-split (inj₁ tt) = inj₁ tt , inj₁ tt
insertion-split (inj₂ [ n ]ˢ) = inj₂ [ n ]ˢ , inj₁ tt
insertion-split (inj₂ (n ∷ s)) = inj₂ [ n ]ˢ , inj₂ s

insertion-sort : LIST → LIST
insertion-sort ℓ = sort (length ℓ) insertion-split ℓ

----------------------
-- merge sort
----------------------

merge-split : LIST → (LIST × LIST)
merge-split (inj₁ tt) = inj₁ tt , inj₁ tt
merge-split (inj₂ [ n ]ˢ) = inj₂ [ n ]ˢ , inj₁ tt
merge-split (inj₂ (n₁ ∷ [ n₂ ]ˢ)) = inj₂ [ n₁ ]ˢ , inj₂ [ n₂ ]ˢ
merge-split (inj₂ (n₁ ∷ (n₂ ∷ s))) with merge-split (inj₂ s)
...| inj₁ tt , inj₁ tt = inj₂ [ n₁ ]ˢ , inj₂ [ n₂ ]ˢ
...| inj₂ [ n ]ˢ , inj₁ tt = inj₂ (n₁  ∷ [ n ]ˢ) , inj₂ [ n₂ ]ˢ
...| inj₂ s₁ , inj₂ s₂ = inj₂ (n₁ ∷ s₁) , inj₂ (n₂ ∷ s₂)
-- not possible
...| inj₂ (n ∷ s') , inj₁ tt =  inj₂ (n ∷ s') , inj₁ tt
...| inj₁ tt_ , inj₂ s' =  inj₁ tt , inj₂ s'

merge-sort : LIST → LIST
merge-sort ℓ = sort (length ℓ) merge-split ℓ
