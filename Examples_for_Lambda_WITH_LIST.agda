-- Time-stamp: <2020-07-04 10:07:29 pierre>
{--------------------------------------------------------------------
© Pierre Lescanne Pierre.Lescanne@ens-lyon.fr      Agda version 2.6.1
                    Examples_for_Lambda_WITH_LIST
  --------------------------------------------------------------------}
module Examples_for_Lambda_WITH_LIST where

open import Lambda
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_)
open import Nat_complement
open import Lambda_WITH_LIST
open import LIST
open import Data.Sum using (_⊎_;[_,_]′;inj₁;inj₂)
open import Data.Unit using (⊤;tt)
open import Data.Maybe

----------
-- in Λin
----------

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

-----------------
-- Examples in Λ
-----------------

ƛƛ01 : Λ
ƛƛ01 = ƛ (ƛ (dB 0 ¤ dB 1))

p_ƛƛ01 : is-lin ƛƛ01 []
p_ƛƛ01 = is-lin-ƛ (is-lin-ƛ (is-lin-¤ is-lin-dB is-lin-dB) (0∷≻0 Seq≻0[])) [0]≻0

t_ƛƛ01 : Λin []
t_ƛƛ01 = Λis-lin→Λin p_ƛƛ01

p'_ƛƛ01 : is-lin ƛƛ01 []
p'_ƛƛ01 = Λin→Λis-lin t_ƛƛ01

ƛƛ01'' : Maybe (Λin [])
ƛƛ01'' = Λ→MaybeΛin ƛƛ01

--

ƛ0_ƛ0 : Λ
ƛ0_ƛ0 = ƛ (dB 0 ¤ ƛ (dB 0))

p_ƛ0_ƛ0 : is-lin ƛ0_ƛ0 []
p_ƛ0_ƛ0 = is-lin-ƛ (is-lin-¤ is-lin-dB (is-lin-ƛ is-lin-dB [0]≻0)) [0]≻0

t_ƛ0_ƛ0 : Λin []
t_ƛ0_ƛ0 = Λis-lin→Λin p_ƛ0_ƛ0

p'_ƛ0_ƛ0 : is-lin ƛ0_ƛ0 []
p'_ƛ0_ƛ0 = Λin→Λis-lin t_ƛ0_ƛ0

ƛ0_ƛ0'' : Maybe (Λin [])
ƛ0_ƛ0'' = Λ→MaybeΛin ƛ0_ƛ0

--

ƛƛ0ƛ20 : Λ
ƛƛ0ƛ20 = ƛ (ƛ (dB 0 ¤ (ƛ (dB 2 ¤ dB 0))))

ƛƛ0ƛ20'' : Maybe (Λin [])
ƛƛ0ƛ20'' = Λ→MaybeΛin ƛƛ0ƛ20

--

ƛ01ƛ20' : Λ
ƛ01ƛ20' = ƛ (dB 0 ¤ dB 1) ¤ ƛ (dB 2 ¤ dB 0)

ƛ01ƛ20 : Λ
ƛ01ƛ20 = ƛ (ƛ ƛ01ƛ20')

ƛ01ƛ20'' : Maybe (Λin [])
ƛ01ƛ20'' = Λ→MaybeΛin ƛ01ƛ20

--
ƛƛ0ƛƛ0ƛ20ƛ30 : Λ
ƛƛ0ƛƛ0ƛ20ƛ30 = ƛ (ƛ (dB 0 ¤ ƛ (ƛ (dB 0 ¤ ƛ (dB 2 ¤ dB 0)) ¤ ƛ (dB 3 ¤ dB 0))))

ƛƛ0ƛƛ0ƛ20ƛ30'' : Maybe (Λin [])
ƛƛ0ƛƛ0ƛ20ƛ30'' = Λ→MaybeΛin ƛƛ0ƛƛ0ƛ20ƛ30

--
ƛƛƛ021 : Λ 
ƛƛƛ021 = ƛ (ƛ (ƛ (dB 0 ¤ (dB 2 ¤ dB 1))))

ƛƛƛ021'' =  Λ→MaybeΛin ƛƛƛ021

