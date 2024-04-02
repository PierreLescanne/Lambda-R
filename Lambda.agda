-- Time-stamp: <2024-04-01 21:56:58 pierre>
module Lambda where

-- open import LinearLambda_R_dB 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_;refl; cong; sym)
open import Data.Bool using (Bool; if_then_else_) renaming (not to ¬_;false to °;true to ¹)
open import Data.Nat using (ℕ; zero; suc)
open import Nat_complement 
open import Data.Maybe
open import Data.List using (List; _++_;[_];_∷ʳ_) renaming ([] to ε;_∷_ to _::_;map to mapL)

-- === Λ ===
data Λ : Set where
  dB : (k : ℕ) → Λ
  _¤_ : Λ → Λ → Λ
  ƛ : (t : Λ) → Λ

-- ========== Linear lambda terms ==========
-- "n" is the openedness. If then openedness is 0, then the terms are closed
mutual 
  data LinΛ : (n : ℕ) → Set where
    dB : (n : ℕ) → (k : ℕ) → (k ≺ n) → LinΛ n
    _¤_ : {n : ℕ} → LinΛ n → LinΛ n → LinΛ n
    ƛ : {n : ℕ} → (t : LinΛ (suc n)) → (0 E! t) → LinΛ n

-- "i E! t" means: i occurs once in t
  data  _E!_ : {n : ℕ} → (i : ℕ) → LinΛ n → Set where
   E!DB : {n i k : ℕ} → (p : k ≺ n) → (i =̂ k) → i E! (dB n k p)
   E!¤L : {n i : ℕ} → {t₁ t₂ : LinΛ n} → i E! t₁ → i ¬E t₂ → i E! (t₁ ¤ t₂)
   E!¤R : {n i : ℕ} → {t₁ t₂ : LinΛ n} → i ¬E t₁ → i E! t₂ → i E! (t₁ ¤ t₂)
   E!ƛ :  {n i : ℕ} → {t : LinΛ (suc n)} → {p : 0 E! t} → suc i E! t → i E! (ƛ t p)

-- "i ¬E t" means: i does not occur in t.
  data _¬E_ : {n : ℕ} → (i : ℕ) → LinΛ n → Set where
   ¬EDB : {n i k : ℕ} → (i ≠ k) → (p : k ≺ n) → i ¬E (dB n k p)
   ¬E¤ : {n i : ℕ} → {t₁ t₂ : LinΛ n} → i ¬E t₁ → i ¬E t₂ → i ¬E (t₁ ¤ t₂)
   ¬Eƛ : {n i : ℕ} → {t : LinΛ (suc n)} → {p : 0 E! t} → suc i ¬E t → i ¬E (ƛ t  p)

-- =========== From LinΛ to Λ  ============
LinΛ→Λ : {n : ℕ} → LinΛ n →  Λ
LinΛ→Λ (dB _ i _) = dB i
LinΛ→Λ (t₁ ¤ t₂) = LinΛ→Λ t₁ ¤ LinΛ→Λ t₂
LinΛ→Λ  (ƛ t _)  = ƛ (LinΛ→Λ t)

-- =========== From Λ to LinΛ  ============
-- ==== tools for the translation ====
-- maybe a proof of i E! t ?
_¬E?_ :  {n : ℕ} → (i : ℕ) → (t : LinΛ n) → Maybe (i ¬E t)
i ¬E? (dB n k p) = caseDB (i ≠? k)
          where caseDB : {i : ℕ} → Maybe (i ≠ k) → Maybe (i ¬E dB n k p)
                caseDB nothing = nothing
                caseDB (just p≠) = just (¬EDB p≠ p)
i ¬E? (ƛ t p) = caseƛ (suc i ¬E? t)
           where caseƛ : {n i : ℕ} → {t : LinΛ (suc n)} → {p : 0 E! t} → Maybe (suc i ¬E t) → Maybe (i ¬E (ƛ t  p))
                 caseƛ nothing = nothing
                 caseƛ (just p) = just (¬Eƛ p)
i ¬E? (t₁ ¤ t₂) = case¤ (i ¬E? t₁) (i ¬E? t₂)
           where case¤ : {n i : ℕ} → {t₁ t₂ : LinΛ n} → Maybe (i ¬E t₁) → Maybe (i ¬E t₂) → Maybe (i ¬E (t₁ ¤ t₂))
                 case¤ nothing _ = nothing
                 case¤ _ nothing = nothing
                 case¤ (just p₁) (just p₂) = just (¬E¤ p₁ p₂)
               
-- maybe a proof of i E! t ?
_E!?_ :  {n : ℕ} → (i : ℕ) → (t : LinΛ n) → Maybe (i E! t)
i E!? (dB n k p) = caseDB (i =̂? k)
          where caseDB : {i : ℕ} → Maybe (i =̂ k) → Maybe (i E! dB n k p)
                caseDB nothing = nothing
                caseDB (just p') = just (E!DB p p') 
i E!? (ƛ t p) = caseƛ (suc i E!? t)
           where caseƛ : {n i : ℕ} → {t : LinΛ (suc n)} → {p : 0 E! t} → Maybe (suc i E! t) → Maybe (i E! (ƛ t  p))
                 caseƛ nothing = nothing
                 caseƛ (just p) = just (E!ƛ p)
i E!? (t₁ ¤ t₂) = choose (i ¬E? t₁) -- or  (i ¬E? t₂)
          where case¤iE!t₁ : {n i : ℕ} → {t₁ t₂ : LinΛ n} → Maybe (i E! t₁) → Maybe ((i ¬E t₂) → i E! (t₁ ¤ t₂))
                case¤iE!t₁ nothing = nothing
                case¤iE!t₁ (just p) = just (E!¤L p)
                
                case¤iE!t₂ : {n i : ℕ} → {t₁ t₂ : LinΛ n} → Maybe (i E! t₂) → Maybe ((i ¬E t₁) → i E! (t₁ ¤ t₂))
                case¤iE!t₂ nothing =  nothing
                case¤iE!t₂ (just p)= just (λ z → E!¤R z p)

                choose : Maybe (i ¬E t₁) → Maybe (i E! (t₁ ¤ t₂))
                choose nothing = ap (case¤iE!t₁ (i E!? t₁)) (i ¬E? t₂)
                choose (just _) = ap (case¤iE!t₂ (i E!? t₂)) (i ¬E? t₁)

-- a translation from Λ terms to closed linear lambda-terms
Λ→LinΛ : {n : ℕ} → Λ →  Maybe (LinΛ n)
Λ→LinΛ {n} (dB k) = casep (k ≺? n)
  where casep : Maybe (k ≺ n) → Maybe (LinΛ n)
        casep nothing = nothing
        casep (just p) = just (dB n k p)
Λ→LinΛ {n} (t₁ ¤ t₂) = build¤ (Λ→LinΛ {n} t₁) (Λ→LinΛ {n} t₂)
        where build¤ : Maybe (LinΛ n) → Maybe (LinΛ n) → Maybe (LinΛ n)
              build¤ nothing _ = nothing
              build¤ _ nothing = nothing
              build¤ (just u₁) (just u₂) = just (u₁ ¤ u₂)
Λ→LinΛ {n} (ƛ t) = buildƛ (Λ→LinΛ {suc n} t) 
                    where buildƛ : Maybe (LinΛ (suc n)) → Maybe (LinΛ n)
                          buildƛ nothing = nothing
                          buildƛ (just u) = buildƛ' (0 E!? u)
                               where buildƛ' : Maybe (0 E! u) → Maybe (LinΛ n)
                                     buildƛ' nothing = nothing
                                     buildƛ' (just p) = just (ƛ u p)

-- a check of the consistency: my goal is to show that Lam→Lam is t → just t, if t is closed and linear.
Lam→Lam : Λ → Maybe Λ 
Lam→Lam t = mbLinLam (Λ→LinΛ t)
        where mbLinLam : Maybe (LinΛ 0) →  Maybe Λ
              mbLinLam nothing = nothing
              mbLinLam (just t) = just (LinΛ→Λ t)

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

-- normalisation in LinΛ
normLinΛ : {n : ℕ} → ℕ → LinΛ n → Maybe (LinΛ n)
normLinΛ {n} k t = case (Λυ→Λ (normΛυ k (Λ→Λυ (LinΛ→Λ t))))
                         where case : Maybe Λ → Maybe (LinΛ n)
                               case nothing = nothing
                               case (just t) = Λ→LinΛ t

