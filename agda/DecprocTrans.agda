module DecprocTrans where

open import lib
open import Tp
open import Decproc
open import ExtraIntegerLemmas

mutual
 trns : ∀{T1 T2 T3}{k k'} →
        T1 < k ] T2 →
        T2 < k' ] T3 →
        T1 < k +ℤ k' ] T3
 trns{k = k}{k'} (NatRefl{n} x) (NatRefl{n'}{m'} x') =
   NatRefl h
   where h : toℤ n ≤ℤ k +ℤ k' +ℤ toℤ m' ≡ tt
         h with keep (k +ℤ k' +ℤ toℤ m')
         h | u , e rewrite e with (≤ℤ-trans{toℤ n} x (≤ℤ-+2a{toℤ n'}{z = k} x'))
         h | u , e | v rewrite trans (sym(+ℤ-assoc{k}{k'}{toℤ m'})) e = v

 trns (Fun{n}{m}{i}{j}{T1}{T2}{T1'}{T2'} x y d dd)
      (Fun{mn}{mm}{ii}{jj}{TT1}{TT2}{TT1'}{TT2'} x' y' d' dd') = Fun ((≤ℤ+{0ℤ}{ii} x' x)) h' (trns d' d) h 
  where h : T2 < negℤ (ii +ℤ i) ] TT2'
        h rewrite negℤ-+{ii}{i} | +ℤcomm{negℤ ii}{negℤ i} = trns dd dd'

        h' : ii +ℤ i ≥ℤ toℤ n -ℤ (j +ℤ jj) -ℤ toℤ mm ≡ tt
        h' with ≤ℤ+2 {toℤ m -ℤ jj -ℤ toℤ mm}{toℤ n -ℤ j -ℤ toℤ m}{ii} {i} y' y
        h' | u rewrite negℤ-+{j}{jj} | +ℤcomm{toℤ m +ℤ negℤ jj +ℤ negℤ (toℤ mm)}{toℤ n +ℤ negℤ j +ℤ negℤ (toℤ m)}
               | +ℤ-assoc{toℤ n +ℤ negℤ j}{negℤ (toℤ m)}{toℤ m +ℤ negℤ jj +ℤ negℤ (toℤ mm)}
               | +ℤ-assoc{toℤ m}{negℤ jj}{negℤ (toℤ mm)}
               | sym (+ℤ-assoc{negℤ (toℤ m)}{toℤ m}{negℤ jj +ℤ negℤ (toℤ mm)})
               | +ℤ-cancel2{toℤ m}
               | sym (+ℤ-assoc{toℤ n +ℤ negℤ j}{negℤ jj}{negℤ (toℤ mm)})
               | +ℤ-assoc{toℤ n}{negℤ j}{negℤ jj} = u