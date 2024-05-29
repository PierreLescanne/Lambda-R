-- Time-stamp: <2024-05-29 17:05:41 pierre>
module Examples_for_LambdaL where

open import LambdaL
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List;[_];_∷_) renaming ([] to ε)

i' : ΛL ε
i' = ƛ (dB 0) okε

-- λxyzu .xyzu.  
xyzu : ΛL (0 ∷ (1 ∷ (2 ∷ [ 3 ])))
xyzu  = ((dB 0 ¤ dB 1) ¤ dB 2) ¤ dB 3

λxyzu : ΛL (0 ∷ (1 ∷ [ 2 ]))
λxyzu = ƛ xyzu okε̸

λλxyzu : ΛL (0 ∷ [ 1 ])
λλxyzu = ƛ (ƛ xyzu okε̸) okε̸

λλλxyzu : ΛL [ 0 ]
λλλxyzu = ƛ (ƛ (ƛ xyzu okε̸) okε̸) okε̸

λλλλxyzu : ΛL ε
λλλλxyzu = ƛ (ƛ (ƛ (ƛ xyzu okε̸) okε̸) okε̸) okε

-- v1
v1 : ΛL ε
v1 = ƛ (ƛ (dB 0 ¤ dB 1) okε̸) okε

v1' : ΛL ε
v1' = ƛ (ƛ (dB 1 ¤ dB 0) okε̸) okε

v4' : ΛL (0 ∷ 1 ∷ (2 ∷ ε))
v4' = (dB 2 ¤ dB 1) ¤ dB 0

v4'' : ΛL ((2 ∷ ε) ‡ (1 ∷ ε))
v4'' = dB 2 ¤ dB 1

db2 : ΛL (2 ∷ ε)
db2 = dB 2

db1 : ΛL (1 ∷ ε)
db1 = dB 1

v4 : ΛL ε
v4 = ƛ (ƛ (ƛ ((dB 2 ¤ dB 1) ¤ dB 0) okε̸) okε̸) okε

v6 : ΛL ε
v6 = ƛ (ƛ (ƛ (ƛ ((dB 3 ¤ dB 2) ¤ (dB 1 ¤ dB 0)) okε̸) okε̸) okε̸) okε

v7 : ΛL ε
v7 = ƛ (ƛ (ƛ ((dB 2 ¤ dB 1) ¤ ƛ (dB 0 ¤ dB 1) okε̸) okε̸) okε̸) okε

v6' : ΛL (((3 ∷ ε) ‡ (2 ∷ ε)) ‡ ((1 ∷ ε) ‡ (0 ∷ ε)))
v6' = (dB 3 ¤ dB 2) ¤ (dB 1 ¤ dB 0)

