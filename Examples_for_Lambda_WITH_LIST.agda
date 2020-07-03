-- Time-stamp: <2020-06-21 21:45:38 pierre>
{--------------------------------------------------------------------
   © Pierre Lescanne                          Agda version 2.6.1
 
                     DO NOT MODIFY THIS FILE

                  Pleased do not modifiy this file.

 If you want to modify it send a mail to Pierre.Lescanne@ens-lyon.fr
 --------------------------------------------------------------------}
module Examples_for_Lambda_WITH_LIST where

open import Lambda
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_)
open import Nat_complement
open import Lambda_WITH_LIST
open import LIST
open import Is-lin
open import Data.Sum using (_⊎_;[_,_]′;inj₁;inj₂)
open import Data.Unit using (⊤;tt)
open import Data.Maybe

-- in Λin
i' : Λin []
i' = ƛ (dB 0) [0]≻0

xyzu : Λin (0 :: (1 :: (2 :: [ 3 ])))
xyzu  = ((dB 0 ¤ dB 1) ¤ dB 2) ¤ dB 3

λxyzu : Λin (0 :: (1 :: [ 2 ]))
λxyzu = ƛ xyzu (0∷≻0 (Seq≻0∷ (Seq≻0∷ Seq≻0[])))

λλxyzu : Λin (0 :: [ 1 ])
λλxyzu = ƛ (ƛ xyzu (0∷≻0 (Seq≻0∷ (Seq≻0∷ Seq≻0[])))) (0∷≻0 (Seq≻0∷ Seq≻0[]))

λλλxyzu : Λin [ 0 ]
λλλxyzu = ƛ (ƛ (ƛ xyzu (0∷≻0 (Seq≻0∷ (Seq≻0∷ Seq≻0[])))) (0∷≻0 (Seq≻0∷ Seq≻0[]))) (0∷≻0 Seq≻0[])

λλλλxyzu : Λin []
λλλλxyzu = ƛ (ƛ (ƛ (ƛ xyzu (0∷≻0 (Seq≻0∷ (Seq≻0∷ Seq≻0[])))) (0∷≻0 (Seq≻0∷ Seq≻0[]))) (0∷≻0 Seq≻0[])) [0]≻0

t1 : Λin []
t1 = ƛ (ƛ (dB 0 ¤ dB 1) (0∷≻0 Seq≻0[])) [0]≻0

t2 : Λin []
t2 = ƛ (ƛ (dB 1 ¤ dB 0) (0∷≻0 Seq≻0[])) [0]≻0

t3 : Λin (0 :: (1 :: [ 2 ]))
t3 = (dB 2 ¤ dB 1) ¤ dB 0

t4 : Λin ([ 2 ] ‡ [ 1 ])
t4 = dB 2 ¤ dB 1

db2 : Λin [ 2 ]
db2 = dB 2

db1 : Λin [ 1 ]
db1 = dB 1

t5 : Λin []
t5 = ƛ (ƛ (ƛ ((dB 2 ¤ dB 1) ¤ dB 0) (0∷≻0 (Seq≻0∷ Seq≻0[]))) (0∷≻0 Seq≻0[])) [0]≻0

t6 : Λin []
t6 = ƛ (ƛ (ƛ (ƛ ((dB 3 ¤ dB 2) ¤ (dB 1 ¤ dB 0)) (0∷≻0 (Seq≻0∷ (Seq≻0∷ Seq≻0[])))) (0∷≻0(Seq≻0∷ Seq≻0[]))) (0∷≻0 Seq≻0[])) [0]≻0

t7 : Λin []
t7 = ƛ (ƛ (ƛ ((dB 2 ¤ dB 1) ¤ ƛ (dB 0 ¤ dB 1) (0∷≻0 Seq≻0[])) (0∷≻0 (Seq≻0∷ Seq≻0[]))) (0∷≻0 Seq≻0[])) [0]≻0

t8 : Λin (([ 3 ] ‡ [ 2 ]) ‡ ([ 1 ] ‡ [ 0 ]))
t8 = (dB 3 ¤ dB 2) ¤ (dB 1 ¤ dB 0)

ex1 : Λin [ 1 ]
ex1 = dB 1

ex2 : Λin [ 0 ]
ex2 = dB 0

ex3 : Λin (0 :: [ 1 ])
ex3 = ex2 ¤ ex1

ex4 : Λin [ 0 ]
ex4 = ƛ (ex2 ¤ ex1) (0∷≻0 Seq≻0[])

ex5 : Λin []
ex5 = ƛ ex4 [0]≻0

-- Examples in Λ

a : Λ
a = ƛ (ƛ (dB 0 ¤ dB 1))

p_a : is-lin a []
p_a = is-lin-ƛ (is-lin-ƛ (is-lin-¤ is-lin-dB is-lin-dB) (0∷≻0 Seq≻0[])) [0]≻0

t_a : Λin []
t_a = Λis-lin→Λin p_a

p'_a : is-lin a []
p'_a = Λin→Λis-lin t_a

a'' : Maybe (Λin [])
a'' = Λ→MaybeΛin a

--

b : Λ
b = ƛ (dB 0 ¤ ƛ (dB 0))

p_b : is-lin b []
p_b = is-lin-ƛ (is-lin-¤ is-lin-dB (is-lin-ƛ is-lin-dB [0]≻0)) [0]≻0

t_b : Λin []
t_b = Λis-lin→Λin p_b

p'_b : is-lin b []
p'_b = Λin→Λis-lin t_b

b'' : Maybe (Λin [])
b'' = Λ→MaybeΛin b

--

c : Λ
c = ƛ (ƛ (dB 0 ¤ (ƛ (dB 2 ¤ dB 0))))

c'' : Maybe (Λin [])
c'' = Λ→MaybeΛin c

--

d' : Λ
d' = ƛ (dB 0 ¤ dB 1) ¤ ƛ (dB 2 ¤ dB 0)

d : Λ
d = ƛ (ƛ d')

d'' : Maybe (Λin [])
d'' = Λ→MaybeΛin d

--
e : Λ
e = ƛ (ƛ (dB 0 ¤ ƛ (ƛ (dB 0 ¤ ƛ (dB 2 ¤ dB 0)) ¤ ƛ (dB 3 ¤ dB 0))))

e'' : Maybe (Λin [])
e'' = Λ→MaybeΛin e

--
f : Λ 
f = ƛ (ƛ (ƛ (dB 0 ¤ (dB 2 ¤ dB 1))))

f'' =  Λ→MaybeΛin f
