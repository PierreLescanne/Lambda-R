-- Time-stamp: <2024-05-29 11:16:22 pierre>
module LambdaL where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_;refl; cong; sym)
open import Data.Maybe using (Maybe; nothing; just; map)
open import Data.Bool using (Bool; if_then_else_) renaming (not to ¬_;false to °;true to ¹)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_)
-- open import Nat_complement 
open import Data.List using (List;_++_;[_];_∷ʳ_) renaming ([] to ε;_∷_ to _::_;map to mapL)
open import Data.Vec using (Vec;[];_∷_;zip;_⊛_;tail;head) renaming (map to mapV)
open import Data.Product using (_×_;_,_;proj₁;proj₂)
open import Data.Sum using (_⊎_;[_,_];inj₁;inj₂)

-- ==================== Comparaisons with booleans  ====================
_<_ : ℕ → ℕ → Bool
0 < (suc _) = ¹
suc n < suc m = n < m
_ < _ = °

-- ==============================
--         ΛL
-- ==============================
-- error-less tail of a list
tl : List ℕ → List ℕ
tl ε = ε
tl (_ :: l) = l

-- error-less map of -1
map↓ : List ℕ → List ℕ
map↓ ε = ε
map↓ (0 :: l) = ε
map↓ ((suc n) :: l) = n :: (map↓ l)

map+1 : List ℕ → List ℕ
map+1 ε = ε
map+1 (n :: l) = suc n :: (map+1 l)

-- like a zipper that zips two ordered lists producing an ordered list;
-- the symbol ‡ reminds a zipper.
_‡_ : List ℕ → List ℕ → List ℕ
l ‡ ε = l
ε ‡ l = l
(x₁ :: l₁) ‡ (x₂ :: l₂) =
  if x₁ < x₂ then x₁ :: (l₁ ‡ (x₂ :: l₂))
  else x₂ :: ((x₁ :: l₁) ‡ l₂)

-- OK0 checks that the (ordered) list starts with 0 and has no other 0
data OK0 : List ℕ → Set where
  okε : OK0 (0 :: ε)
  okε̸ : {n : ℕ} → {ℓ : List ℕ} → OK0 (0 :: suc  n :: ℓ)

OK0? : (l : List ℕ) → Maybe (OK0 l)
OK0? (0 :: ε) = just okε
OK0? (0 :: (suc n) :: _) = just okε̸
OK0? _ = nothing

-- ==========================================================================
data ΛL : (ℓ : List ℕ) → Set where
  dB : (k : ℕ) → ΛL [ k ]
  ƛ : {ℓ : List ℕ} → ΛL ℓ → OK0 ℓ → ΛL (map↓ (tl ℓ))
  _¤_ :  {ℓ₁ ℓ₂ : List ℕ} → ΛL ℓ₁ → ΛL ℓ₂ → ΛL (ℓ₁ ‡ ℓ₂)
-- ==========================================================================

-- ==============================
--          Normalisation
-- ==============================
-- === Λ ===
data Λ : Set where
  dB : (k : ℕ) → Λ
  _¤_ : Λ → Λ → Λ
  ƛ : (t : Λ) → Λ

-- ==========================================
-- ========== Explicit subtitutions =========
-- ========== strong normalisation ==========
-- ==========================================

mutual 
  data Λυ : Set where
    dB : (k : ℕ) → Λυ
    _¤_ : Λυ  → Λυ  → Λυ 
    ƛ : Λυ → Λυ 
    _〚_〛 : Λυ → Συ → Λυ 

  data Συ : Set where 
    _/ : Λυ → Συ
    ⇑_ : Συ → Συ
    ↑ : Συ

-- ========== From Λ to Λυ ==========
Λ→Λυ : Λ → Λυ
Λ→Λυ (dB k) = (dB k)
Λ→Λυ (ƛ t) = ƛ (Λ→Λυ t)
Λ→Λυ (t₁ ¤ t₂) = (Λ→Λυ t₁) ¤ (Λ→Λυ t₂)

-- ========== From Λυ to Λ ==========
Λυ→Λ : Λυ → Maybe Λ
Λυ→Λ (dB k) = just (dB k)
Λυ→Λ (ƛ t) = case (Λυ→Λ t)
         where case : Maybe Λ → Maybe Λ
               case nothing = nothing
               case (just t) = just (ƛ t)
Λυ→Λ (t₁ ¤ t₂) = case (Λυ→Λ t₁) (Λυ→Λ t₂)
         where case : Maybe Λ → Maybe Λ → Maybe Λ
               case nothing _ = nothing
               case _ nothing = nothing
               case (just u₁) (just u₂) = just (u₁ ¤ u₂)
Λυ→Λ (_ 〚 _ 〛)  = nothing

-- β contraction
contractβ : Λυ → Λυ
contractβ (((ƛ t₁) ¤ t₂)) = t₁ 〚 t₂ / 〛
contractβ t = t

-- υ contraction
contractυ : Λυ → Λυ
contractυ (ƛ t 〚 s 〛) = ƛ (t 〚 ⇑ s 〛)
contractυ ((t₁ ¤ t₂)〚 s 〛) = (t₁ 〚 s 〛) ¤ (t₂ 〚 s 〛)
contractυ (dB 0 〚 t / 〛) = t
contractυ (dB (suc k) 〚 t / 〛) = dB k
contractυ (dB 0 〚 ⇑ _ 〛) = dB 0
contractυ (dB (suc k) 〚 ⇑ s 〛) = (dB k 〚 s 〛) 〚 ↑ 〛
contractυ (dB k 〚 ↑ 〛) = dB (suc k)
contractυ t = t

-- distribute substitutions
contractυ* : ℕ → Λυ → Λυ
contractυ* (suc k) ((t 〚 s 〛)〚 s' 〛) = contractυ* k (contractυ* k (contractυ (t 〚 s 〛)) 〚 s' 〛)
contractυ* (suc k) (t 〚 s 〛) = contractυ* k (contractυ (t 〚 s 〛))
contractυ* 0 (t 〚 s 〛) = t 〚 s 〛
contractυ* k (t₁ ¤ t₂) = (contractυ* k t₁) ¤ (contractυ* k t₂)
contractυ* k (ƛ t) = ƛ (contractυ* k t)
contractυ* _ (dB k) = dB k

-- normalisation in Λυ 
normΛυ : ℕ → Λυ → Λυ
normΛυ (suc k) ((ƛ t₁) ¤ t₂) = normΛυ k (contractυ* (suc k) (t₁ 〚 t₂ / 〛))
normΛυ k ((dB i) ¤ t) = dB i ¤ normΛυ k t
normΛυ (suc k) (t₁ ¤ t₂) = normΛυ k ((normΛυ (suc k) t₁) ¤ normΛυ (suc k) t₂)
normΛυ (suc k) (t 〚 s 〛) = normΛυ k (contractυ* (suc k) (t 〚 s 〛))
normΛυ k (ƛ t) = ƛ (normΛυ k t)
normΛυ k t = t

-- ==============================
--         Translations
-- ==============================
ΛL→Λ : {l : List ℕ} → ΛL l → Λ 
ΛL→Λ (dB k) = dB k
ΛL→Λ (ƛ t _) = ƛ (ΛL→Λ t)
ΛL→Λ (t₁ ¤ t₂) = ΛL→Λ t₁ ¤ ΛL→Λ t₂

-- we assume that the term in Λ is linear and hence its list of indices is sorted
listInd : Λ → List ℕ
listInd (dB k) = [ k ]  -- sorted 
listInd (t₁ ¤ t₂) = listInd t₁ ‡ listInd t₂ --preserves sortedness
listInd (ƛ t) = map↓ (tl (listInd t)) --preserves sortedness
        
Λ→ΛL : (t : Λ) → Maybe (ΛL (listInd t))
Λ→ΛL (dB k) =  just (dB k)
Λ→ΛL (t₁ ¤ t₂) = f (Λ→ΛL t₁) (Λ→ΛL t₂)
  where f  : {l₁ l₂ : List ℕ} → Maybe (ΛL l₁) → Maybe (ΛL l₂) → Maybe (ΛL (l₁ ‡ l₂))
        f (just u₁) (just u₂) = just (u₁ ¤ u₂) 
        f _ _ = nothing
Λ→ΛL (ƛ t) = buildƛ (Λ→ΛL t)
  where buildƛ : Maybe (ΛL (listInd t)) → Maybe (ΛL (listInd (ƛ t)))
        buildƛ nothing = nothing
        buildƛ (just u) = buildƛ' (OK0? (listInd t))
          where buildƛ' : Maybe (OK0 (listInd t)) → Maybe (ΛL (listInd (ƛ t)))
                buildƛ' nothing = nothing
                buildƛ' (just p) = just (ƛ u p)
-- ==============================
-- strong normalisation in ΛL
-- ==============================

MbListInd : Maybe Λ → List ℕ
MbListInd nothing = ε
MbListInd (just t) = listInd t

MbΛ→MbΛL : (t : Maybe Λ) → Maybe (ΛL (MbListInd t))
MbΛ→MbΛL nothing = nothing
MbΛ→MbΛL (just t) = Λ→ΛL t

limit' = 7

normΛL : {l : List ℕ} → (t : ΛL l) → Maybe (ΛL (MbListInd (Λυ→Λ (normΛυ limit' (Λ→Λυ (ΛL→Λ t))))))
normΛL t = MbΛ→MbΛL (Λυ→Λ (normΛυ limit' (Λ→Λυ (ΛL→Λ t))))
