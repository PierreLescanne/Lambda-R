-- Time-stamp: <2020-06-22 12:27:06 pierre>
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
  ƛ : {ℓ : LIST} → Λin ℓ → (p : is-0∷LIST≻0 ℓ) → Λin (↓ p)
  _¤_ :  {ℓ₁ ℓ₂ : LIST} → Λin ℓ₁ → Λin ℓ₂ → Λin (ℓ₁ ‡ ℓ₂)
-- =======================================================

Λin→Λ : {ℓ : LIST} → Λin ℓ → Λ 
Λin→Λ (dB k) = dB k
Λin→Λ (ƛ t _) = ƛ (Λin→Λ t)
Λin→Λ (t₁ ¤ t₂) = Λin→Λ t₁ ¤ Λin→Λ t₂

data is-lin : (t : Λ) → (ℓ : LIST) → Set where
  is-lin-dB : {k : ℕ} → is-lin (dB k) [ k ]
  is-lin-ƛ : {t : Λ} → {ℓ : LIST} → is-lin t ℓ → (p : is-0∷LIST≻0 ℓ) → is-lin (ƛ t) (↓ p)
  is-lin-¤ : {t₁ t₂ : Λ} → {ℓ₁ ℓ₂ : LIST} → is-lin t₁ ℓ₁ → is-lin t₂ ℓ₂  → is-lin (t₁ ¤ t₂) (ℓ₁ ‡ ℓ₂)

Λis-lin→Λin : {t : Λ} → {ℓ : LIST} → (is-lin t ℓ) → Λin ℓ
Λis-lin→Λin (is-lin-dB {k}) = dB k
Λis-lin→Λin (is-lin-ƛ p p') = ƛ (Λis-lin→Λin p) p'
Λis-lin→Λin (is-lin-¤ p₁ p₂) = Λis-lin→Λin p₁ ¤ Λis-lin→Λin p₂

Λin→Λis-lin : {ℓ : LIST} → (t : Λin ℓ) → is-lin (Λin→Λ t) ℓ
Λin→Λis-lin (dB _) = is-lin-dB
Λin→Λis-lin (ƛ t p) = is-lin-ƛ (Λin→Λis-lin t) p
Λin→Λis-lin (t₁ ¤ t₂) = is-lin-¤ (Λin→Λis-lin t₁) (Λin→Λis-lin t₂)

