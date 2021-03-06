Require Export SepTypes.OrderedType.
Require Export SepTypes.OExpr.


(***
 *** The monad typeclass
 ***)

Class MonadOps M `{OTypeF M} : Type :=
  { return_ofun : forall {A} `{OType A}, A -o> M A _;
    bind_ofun : forall {A B} `{OType A} `{OType B},
        M A _ -o> (A -o> M B _) -o> M B _ }.

Notation oreturn := (oconst return_ofun).
Notation obind := (oconst bind_ofun).
(*
Definition oreturn {ctx} `{MonadOps} {A} `{OType A} : OExpr ctx (A -o> M A _) :=
  oconst return_ofun.
Definition obind {ctx} `{MonadOps} {A B} `{OType A} `{OType B} :
  OExpr ctx (M A _ -o> (A -o> M B _) -o> M B _) :=
  oconst bind_ofun.
*)
Notation "'do' x <- m1 ; m2" :=
  (obind @o@ m1 @o@ mkLam (fun x => m2))
    (at level 60, m1 at level 59, right associativity).


Class Monad M `{MonadOps M} : Prop :=
  {
    monad_return_bind :
      forall {ctx A B} `{OType A} `{OType B} (f: OExpr ctx (A -o> M B _)) x,
        obind @o@ (oreturn @o@ x) @o@ f =o= f @o@ x;

    monad_bind_return :
      forall {ctx A} `{OType A} (m: OExpr ctx (M A _)),
        obind @o@ m @o@ oreturn =o= m;

    monad_assoc_raw :
      forall {ctx A B C} `{OType A} `{OType B} `{OType C}
             m (f: OExpr ctx (A -o> M B _)) (g: OExpr ctx (B -o> M C _)),
        obind @o@ (obind @o@ m @o@ f) @o@ g
        =o=
        obind @o@ m @o@ (ofun x => obind @o@ (ovar f @o@ ovar x) @o@ ovar g);
  }.

(* This version of associativity of bind is easier to use in practice, because
it does the weakening for you *)
Lemma monad_assoc `{Monad} {ctx A B C} `{OType A} `{OType B} `{OType C}
      m (f: OExpr ctx (A -o> M B _)) (f': OExpr (ctx :> A) (A -o> M B _))
      (g: OExpr ctx (B -o> M C _)) (g': OExpr (ctx :> A) (B -o> M C _))
      {wf: WeakensTo f (PreExtendsToBase _) f'}
      {wg: WeakensTo g (PreExtendsToBase _) g'} :
  obind @o@ (obind @o@ m @o@ f) @o@ g
  =o=
  obind @o@ m @o@ (ofun x => obind @o@ (f' @o@ ovar x) @o@ g').
Proof.
  unfold WeakensTo in * |- *. simpl in wf; simpl in wg.
  rewrite monad_assoc_raw. f_equiv. apply mkLamExt. f_equiv.
  - f_equiv. rewrite <- wf. reflexivity.
  - rewrite <- wg. reflexivity.
Qed.


(***
 *** The Identity Monad
 ***)

Definition Identity A `{OType A} := A.

Instance OTypeF_Identity : OTypeF Identity :=
  fun _ ot => ot.

Instance IdMonad_MonadOps : MonadOps Identity :=
  { return_ofun := fun A _ => oexpr (ofun x => x);
    bind_ofun := fun A B _ _ =>
                   oexpr (ofun m => ofun (f : A -o> B ) => ovar f @o@ ovar m) }.

Instance IdMonad : Monad Identity.
Proof.
  constructor; intros; apply funOExt; intros; simpl; reflexivity.
Qed.
