Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import FunctionNinjas.All.
Require Import Monad.All.

Import ListNotations.
Local Open Scope N.

Module StateMonad.
  Definition t (S : Type) (A : Type) : Type := S -> A * S.

  Instance i (S : Type) : Monad.C (t S) := {
    ret := fun _ x s => (x, s);
    bind := fun _ _ x f s =>
      let (x, s) := x s in
      f x s }.

  Definition get {S : Type} (_ : unit) : t S S :=
    fun s => (s, s).

  Definition set {S : Type} (s : S) : t S unit :=
    fun _ => (tt, s).

  Definition apply {S : Type} (f : S -> S) : t S unit :=
    fun s => (tt, f s).

  Definition run {S A : Type} (s : S) (x : t S A) : A * S :=
    x s.
End StateMonad.

Module Iterable.
  Class C (T : Type -> Type) : Type := {
    iter : forall (M : Type -> Type) `{Monad.C M} {A : Type},
      T A -> (A -> M unit) -> M unit }.

  Module Instance.
    Instance list : C list := {
      iter := fun M _ A =>
        fix iter (l : list A) (f : A -> M unit) : M unit :=
          match l with
          | [] => Monad.ret tt
          | x :: l => Monad.bind (f x) (fun _ => iter l f)
          end }.
  End Instance.

  Definition length {T : Type -> Type} `{C T} {A : Type} (l : T A) : N :=
    snd (StateMonad.run 0 @@ iter (StateMonad.t N) l (fun _ =>
      StateMonad.apply N.succ)).
End Iterable.