-- Time-stamp: <2020-07-03 21:54:31 pierre>
{--------------------------------------------------------------------
   © Pierre Lescanne                          Agda version 2.6.1
 
                     DO NOT MODIFY THIS FILE

                  Pleased do not modifiy this file.

 If you want to modify it send a mail to Pierre.Lescanne@ens-lyon.fr
 --------------------------------------------------------------------}
module Lambda_WITH_LIST where

open import Lambda
open import Data.Bool using (Bool; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_)
open import Data.Maybe
open import Nat_complement 
open import LIST
open import Data.List using (List; map; _++_) renaming (_∷_ to _:l:_; [] to ε)
open import Data.Sum using (_⊎_;[_,_]′;inj₁;inj₂)
open import Data.Product using (_×_;_,_;proj₁;proj₂)
open import Data.Unit using (⊤;tt)

-- =============================================================
-- ==== Here there is a presentation of linear lambda terms ==== 
-- ==== based on ordered sorted lists of de Bruijn indices  ====
-- =============================================================

-- ======================================================
data Λin : (ℓ : LIST) → Set where
  dB : (k : ℕ) → Λin [ k ]
  ƛ : {ℓ : LIST} → Λin ℓ → (p : ℓ ∈-LIST-ℕ⁺) → Λin (↓ p)
  _¤_ :  {ℓ₁ ℓ₂ : LIST} → Λin ℓ₁ → Λin ℓ₂ → Λin (ℓ₁ ‡ ℓ₂)
-- =======================================================

Λin→Λ : {ℓ : LIST} → Λin ℓ → Λ 
Λin→Λ (dB k) = dB k
Λin→Λ (ƛ t _) = ƛ (Λin→Λ t)
Λin→Λ (t₁ ¤ t₂) = Λin→Λ t₁ ¤ Λin→Λ t₂

-- is-lin is a predicate which says the a given term is linear
data is-lin : (t : Λ) → (ℓ : LIST) → Set where
  is-lin-dB : {k : ℕ} → is-lin (dB k) [ k ]
  is-lin-ƛ : {t : Λ} → {ℓ : LIST} → is-lin t ℓ → (p : ℓ ∈-LIST-ℕ⁺) → is-lin (ƛ t) (↓ p)
  is-lin-¤ : {t₁ t₂ : Λ} → {ℓ₁ ℓ₂ : LIST} → is-lin t₁ ℓ₁ → is-lin t₂ ℓ₂  → is-lin (t₁ ¤ t₂) (ℓ₁ ‡ ℓ₂)

-- Is a given LIST linear ?
-- the implementation is limited LIST's of size at most 3 with indices 0, 1, 2, 
is-lin? : (t : Λ) → (ℓ : LIST) → Maybe (is-lin t ℓ)
is-lin-¤? : (t₁ t₂ : Λ) → (ℓ₁ ℓ₂ : LIST) → Maybe (is-lin (t₁ ¤ t₂) (ℓ₁ ‡ ℓ₂))

is-lin-¤? t₁ t₂ ℓ₁ ℓ₂ with is-lin? t₁ ℓ₁
is-lin-¤? t₁ t₂ ℓ₁ ℓ₂ | (just p₁) with is-lin? t₂ ℓ₂
is-lin-¤? t₁ t₂ ℓ₁ ℓ₂ | (just p₁) | (just p₂) = just (is-lin-¤ p₁ p₂)
is-lin-¤? t₁ t₂ ℓ₁ ℓ₂ | (just p₁) | nothing = nothing
is-lin-¤? t₁ t₂ ℓ₁ ℓ₂ | nothing = nothing

-- a very pedestrian and dummy implementation
is-lin? (dB 0) (inj₂ [ 0 ]ˢ) = just is-lin-dB
is-lin? (dB 1) (inj₂ [ 1 ]ˢ) = just is-lin-dB
is-lin? (dB 2) (inj₂ [ 2 ]ˢ) = just is-lin-dB
is-lin? (dB 3) (inj₂ [ 3 ]ˢ) = just is-lin-dB
is-lin? (dB _) _ = nothing
-- ƛ
is-lin? (ƛ t) (inj₁ _)  with (is-lin? t (inj₂ [ 0 ]ˢ))
... | nothing = nothing
... | just p = just (is-lin-ƛ  p [0]≻0)
is-lin? (ƛ t) (inj₂  [ 0 ]ˢ) with (is-lin? t (inj₂ (0 ∷ [ 1 ]ˢ)))
... | nothing = nothing
... | just p = just (is-lin-ƛ p (0∷≻0 Seq≻0[]))
is-lin? (ƛ t) (inj₂  [ 1 ]ˢ) with (is-lin? t (inj₂ (0 ∷ [ 2 ]ˢ)))
... | nothing = nothing
... | just p = just (is-lin-ƛ p (0∷≻0 Seq≻0[]))
is-lin? (ƛ t) (inj₂  [ 2 ]ˢ) with (is-lin? t (inj₂ (0 ∷ [ 3 ]ˢ)))
... | nothing = nothing
... | just p = just (is-lin-ƛ p (0∷≻0 Seq≻0[]))
is-lin? (ƛ t) (inj₂  (0 ∷ [ 1 ]ˢ)) with (is-lin? t (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))))
... | nothing = nothing
... | just p = just (is-lin-ƛ p (0∷≻0 (Seq≻0∷ Seq≻0[])))
is-lin? (ƛ t) (inj₂  (0 ∷ [ 2 ]ˢ)) with (is-lin? t (inj₂ (0 ∷ (1 ∷ [ 3 ]ˢ))))
... | nothing = nothing
... | just p = just (is-lin-ƛ p (0∷≻0 (Seq≻0∷ Seq≻0[])))
is-lin? (ƛ t) (inj₂  (1 ∷ [ 2 ]ˢ)) with (is-lin? t (inj₂ (0 ∷ (2 ∷ [ 3 ]ˢ))))
... | nothing = nothing
... | just p = just (is-lin-ƛ p (0∷≻0 (Seq≻0∷ Seq≻0[])))
is-lin? (ƛ t) (inj₂  (0 ∷ (1 ∷ [ 2 ]ˢ))) with (is-lin? t (inj₂ (0 ∷ (1 ∷ (2 ∷ [ 3 ]ˢ)))))
... | nothing = nothing
... | just p = just (is-lin-ƛ p (0∷≻0 (Seq≻0∷ (Seq≻0∷ Seq≻0[]))))
is-lin? (ƛ t) _ = nothing
-- ¤
is-lin? (t₁ ¤ t₂) (inj₁ _) with is-lin? t₁ (inj₁ _)
is-lin? (t₁ ¤ t₂) (inj₁ _) | nothing = nothing
is-lin? (t₁ ¤ t₂) (inj₁ _) | just p₁ with is-lin? t₂ (inj₁ _)
is-lin? (t₁ ¤ t₂) (inj₁ _) | just p₁ | nothing = nothing
is-lin? (t₁ ¤ t₂) (inj₁ _) | just p₁ | just p₂ = just (is-lin-¤ p₁ p₂)
----
is-lin? (t₁ ¤ t₂) (inj₂ [ k ]ˢ) with is-lin-¤? t₁ t₂ (inj₂ [ k ]ˢ) (inj₁ _)
is-lin? (t₁ ¤ t₂) (inj₂ [ k ]ˢ) | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ [ k ]ˢ) | nothing with is-lin-¤? t₁ t₂ (inj₁ _) (inj₂ [ k ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ [ k ]ˢ) | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ [ k ]ˢ) | nothing | nothing = nothing 
----
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 1 ]ˢ)) with is-lin-¤? t₁ t₂ (inj₂ (0 ∷ [ 1 ]ˢ)) (inj₁ _)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 1 ]ˢ)) | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 1 ]ˢ)) | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 0 ]ˢ) (inj₂ [ 1 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 1 ]ˢ)) | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 1 ]ˢ)) | nothing | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 1 ]ˢ) (inj₂ [ 0 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 1 ]ˢ)) | nothing | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 1 ]ˢ)) | nothing | nothing | nothing with is-lin-¤? t₁ t₂ (inj₁ _) (inj₂ (0 ∷ [ 1 ]ˢ))
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 1 ]ˢ)) | nothing | nothing | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 1 ]ˢ)) | nothing | nothing | nothing | nothing = nothing
----
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 2 ]ˢ)) with is-lin-¤? t₁ t₂ (inj₂ (0 ∷ [ 2 ]ˢ)) (inj₁ _)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 2 ]ˢ)) | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 2 ]ˢ)) | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 0 ]ˢ) (inj₂ [ 2 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 2 ]ˢ)) | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 2 ]ˢ)) | nothing | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 2 ]ˢ) (inj₂ [ 0 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 2 ]ˢ)) | nothing | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 2 ]ˢ)) | nothing | nothing | nothing with is-lin-¤? t₁ t₂ (inj₁ _) (inj₂ (0 ∷ [ 2 ]ˢ))
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 2 ]ˢ)) | nothing | nothing | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 2 ]ˢ)) | nothing | nothing | nothing | nothing = nothing
----
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 3 ]ˢ)) with is-lin-¤? t₁ t₂ (inj₂ (0 ∷ [ 3 ]ˢ)) (inj₁ _)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 3 ]ˢ)) | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 3 ]ˢ)) | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 0 ]ˢ) (inj₂ [ 3 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 3 ]ˢ)) | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 3 ]ˢ)) | nothing | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 3 ]ˢ) (inj₂ [ 0 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 3 ]ˢ)) | nothing | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 3 ]ˢ)) | nothing | nothing | nothing with is-lin-¤? t₁ t₂ (inj₁ _) (inj₂ (0 ∷ [ 3 ]ˢ))
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 3 ]ˢ)) | nothing | nothing | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ [ 3 ]ˢ)) | nothing | nothing | nothing | nothing = nothing
----
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 2 ]ˢ)) with is-lin-¤? t₁ t₂ (inj₂ (1 ∷ [ 2 ]ˢ)) (inj₁ _)
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 2 ]ˢ)) | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 2 ]ˢ)) | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 1 ]ˢ) (inj₂ [ 2 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 2 ]ˢ)) | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 2 ]ˢ)) | nothing | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 2 ]ˢ) (inj₂ [ 1 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 2 ]ˢ)) | nothing | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 2 ]ˢ)) | nothing | nothing | nothing with is-lin-¤? t₁ t₂ (inj₁ _) (inj₂ (1 ∷ [ 2 ]ˢ))
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 2 ]ˢ)) | nothing | nothing | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 2 ]ˢ)) | nothing | nothing | nothing | nothing = nothing
----
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 3 ]ˢ)) with is-lin-¤? t₁ t₂ (inj₂ (1 ∷ [ 3 ]ˢ)) (inj₁ _)
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 3 ]ˢ)) | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 3 ]ˢ)) | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 1 ]ˢ) (inj₂ [ 3 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 3 ]ˢ)) | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 3 ]ˢ)) | nothing | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 3 ]ˢ) (inj₂ [ 1 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 3 ]ˢ)) | nothing | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 3 ]ˢ)) | nothing | nothing | nothing with is-lin-¤? t₁ t₂ (inj₁ _) (inj₂ (1 ∷ [ 3 ]ˢ))
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 3 ]ˢ)) | nothing | nothing | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (1 ∷ [ 3 ]ˢ)) | nothing | nothing | nothing | nothing = nothing
----
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) with is-lin-¤? t₁ t₂ (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) (inj₁ _)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | just p = just p
-- 0 1 ‡ 2
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing with is-lin-¤? t₁ t₂ (inj₂ (0 ∷ [ 1 ]ˢ)) (inj₂ [ 2 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | just p = just p
-- 0 2 ‡ 1
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing with is-lin-¤? t₁ t₂ (inj₂ (0 ∷ [ 2 ]ˢ)) (inj₂ [ 1 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing | just p = just p
-- 1 2 ‡ 0
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing | nothing with is-lin-¤? t₁ t₂ (inj₂ (1 ∷ [ 2 ]ˢ)) (inj₂ [ 0 ]ˢ)
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing | nothing | just p = just p
-- 0 ‡ 1 2
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing | nothing | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 0 ]ˢ) (inj₂ (1 ∷ [ 2 ]ˢ))
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing | nothing | nothing | just p = just p
-- 1 ‡ 0 2
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing | nothing | nothing | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 1 ]ˢ) (inj₂ (0 ∷ [ 2 ]ˢ))
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing | nothing | nothing | nothing | just p = just p
-- 2 ‡ 0 1
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing | nothing | nothing | nothing | nothing with is-lin-¤? t₁ t₂ (inj₂ [ 2 ]ˢ) (inj₂ (0 ∷ [ 1 ]ˢ))
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing | nothing | nothing | nothing | nothing | just p = just p
-- [] ‡ 0 1 2
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing | nothing | nothing | nothing | nothing | nothing with is-lin-¤? t₁ t₂ (inj₁ _) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ)))
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing | nothing | nothing | nothing | nothing | nothing | just p = just p
is-lin? (t₁ ¤ t₂) (inj₂ (0 ∷ (1 ∷ [ 2 ]ˢ))) | nothing | nothing | nothing | nothing | nothing | nothing | nothing | nothing = nothing
--
is-lin? (t₁ ¤ t₂) _ = nothing

------------------------
-- From linear Λ to Λin
------------------------

Λis-lin→Λin : {t : Λ} → {ℓ : LIST} → (is-lin t ℓ) → Λin ℓ
Λis-lin→Λin (is-lin-dB {k}) = dB k
Λis-lin→Λin (is-lin-ƛ p p') = ƛ (Λis-lin→Λin p) p'
Λis-lin→Λin (is-lin-¤ p₁ p₂) = Λis-lin→Λin p₁ ¤ Λis-lin→Λin p₂

------------------------
-- From Λin to linear Λ
------------------------

Λin→Λis-lin : {ℓ : LIST} → (t : Λin ℓ) → is-lin (Λin→Λ t) ℓ
Λin→Λis-lin (dB _) = is-lin-dB
Λin→Λis-lin (ƛ t p) = is-lin-ƛ (Λin→Λis-lin t) p
Λin→Λis-lin (t₁ ¤ t₂) = is-lin-¤ (Λin→Λis-lin t₁) (Λin→Λis-lin t₂)

-----------------
-- From Λ to Λin
-----------------

Λ→MaybeΛin : (t : Λ) → Maybe (Λin [])
Λ→MaybeΛin t with is-lin? t []
... | nothing = nothing
... | just p = just (Λis-lin→Λin p)

------------------------
-- normalization in Λin
------------------------
normΛin : ℕ → Λin [] → Maybe (Λin [])
normΛin k t with (Λυ→Λ (normΛυ k (Λ→Λυ (Λin→Λ t))))
... | just t' = Λ→MaybeΛin t'
... | nothing = nothing

