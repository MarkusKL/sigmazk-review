From SigmaZK Require Import Base Sigma Shrink Parallel.

Section Adjust.
(* Adjust the challenge space of a protocol to match C'. *)

Context {H W Forb : finType} {C C' : nat}.
Context {R : H → W → Prop} {Err : Forb → Prop}.
Context (P : sigma 'I_C R Err).
Context (CBig : (1 < C)%N).

Fixpoint Paralleln1 n : sigma 'I_(C ^ n.+1) R Err :=
  match n with
  | 0 => P
  | n.+1 => Parallel P (Paralleln1 n)
  end.

Program Definition Paralleln n : sigma 'I_(C ^ n) R Err :=
  match n with
  | 0 => Shrink (ltnW CBig) P
  | n.+1 => Paralleln1 n
  end.

Program Definition Adjust : sigma 'I_C' R Err :=
  Shrink (up_logP _ CBig) (Paralleln (up_log C C')).

End Adjust.
