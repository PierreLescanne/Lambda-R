-- Time-stamp: <2024-05-29 17:38:47 pierre>
module Examples_for_LambdaL where

open import LambdaL
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List;[_];_∷_) renaming ([] to ε)

-- open terms
-- Beware: names (identifiers) are just a help, no imposed constraint
-- you can call them foo or bar
λx·x : ΛL ε
λx·x = ƛ (dB 0) okε

xyzu : ΛL (0 ∷ (1 ∷ (2 ∷ [ 3 ])))
xyzu  = ((dB 0 ¤ dB 1) ¤ dB 2) ¤ dB 3

λx·xyzu : ΛL (0 ∷ (1 ∷ [ 2 ]))
λx·xyzu = ƛ xyzu okε̸

λxy·xyzu : ΛL (0 ∷ [ 1 ])
λxy·xyzu = ƛ (ƛ xyzu okε̸) okε̸

λxyz·xyzu : ΛL [ 0 ]
λxyz·xyzu = ƛ (ƛ (ƛ xyzu okε̸) okε̸) okε̸


-- several closed terms

λxy·xy : ΛL ε
λxy·xy = ƛ (ƛ (dB 0 ¤ dB 1) okε̸) okε

λxy·yx : ΛL ε
λxy·yx  = ƛ (ƛ (dB 1 ¤ dB 0) okε̸) okε

λxyzu·xyzu : ΛL ε
λxyzu·xyzu = ƛ (ƛ (ƛ (ƛ xyzu okε̸) okε̸) okε̸) okε

-- several open terms

λxyz·zyx : ΛL (0 ∷ 1 ∷ (2 ∷ ε))
λxyz·zyx = (dB 2 ¤ dB 1) ¤ dB 0

λx·zy : ΛL ((2 ∷ ε) ‡ (1 ∷ ε))
λx·zy = dB 2 ¤ dB 1

λxy·z : ΛL (2 ∷ ε)
λxy·z = dB 2

λx·y : ΛL (1 ∷ ε)
λx·y = dB 1

-- more complex ones (for fun)

v4 : ΛL ε
v4 = ƛ (ƛ (ƛ ((dB 2 ¤ dB 1) ¤ dB 0) okε̸) okε̸) okε

v6 : ΛL ε
v6 = ƛ (ƛ (ƛ (ƛ ((dB 3 ¤ dB 2) ¤ (dB 1 ¤ dB 0)) okε̸) okε̸) okε̸) okε

v7 : ΛL ε
v7 = ƛ (ƛ (ƛ ((dB 2 ¤ dB 1) ¤ ƛ (dB 0 ¤ dB 1) okε̸) okε̸) okε̸) okε

v6' : ΛL (((3 ∷ ε) ‡ (2 ∷ ε)) ‡ ((1 ∷ ε) ‡ (0 ∷ ε)))
v6' = (dB 3 ¤ dB 2) ¤ (dB 1 ¤ dB 0)

