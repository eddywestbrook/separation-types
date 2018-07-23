Require Export SepTypes.Monad.

(***
 *** Monads with Fixed-points
 ***)

Class MonadFixOps M `{OTypeF M} : Type :=
  { fixM : forall {A B} `{OType A} `{OType B},
      ((A -o> M B _) -o> (A -o> M B _)) -o> (A -o> M B _); }.

Definition ofix {ctx} `{MonadFixOps} {A B} `{OType A} `{OType B} :
  OExpr ctx (((A -o> M B _) -o> (A -o> M B _)) -o> (A -o> M B _)) :=
  const_ofun fixM.


Class MonadFix M {OF:OTypeF M} `{@MonadOps M OF} `{@MonadFixOps M OF} : Prop :=
  { Monad_MonadFix :> Monad M;
    FixedPoint_ofix :
      forall {ctx A B} `{OType A} `{OType B}
             (f: OExpr ctx ((A -o> M B _) -o> (A -o> M B _))),
        ofix @o@ f =o= f @o@ (ofix @o@ f)
  }.

Class MonadBottomOps M `{OTypeF M} : Type :=
  { bottomM : forall {A} `{OType A}, M A _ }.

Definition obottom {ctx} `{MonadBottomOps} {A} `{OType A} : OExpr ctx (M A _) :=
  const_ofun bottomM.

Class MonadBottom M {OF:OTypeF M} `{@MonadOps M OF}
      `{@MonadBottomOps M OF} : Prop :=
  { Monad_MonadBottom :> Monad M;
    Bottom_MonadBottom : forall {ctx A} `{OType A} (m: OExpr ctx (M A _)),
        obottom <o= m }.


(***
 *** The Fixed-point Monad = Downwards-closed sets
 ***)

(* The type of downward-closed sets *)
Definition DownSet A `{OType A} := Flip A -o> Prop.

Instance OTypeF_DownSet : OTypeF DownSet := fun _ _ => _.

(* The Monad operations for downward-closed sets *)
Instance MonadOps_DownSet : MonadOps DownSet :=
  {| returnM :=
       fun A _ =>
         oexpr (ofun (x:A) => ofun (y:Flip A) => oappr @o@ ovar y @o@ ovar x);
     bindM :=
       fun A B _ _ =>
         oexpr (ofun m => ofun f => ofun (y:Flip B) =>
                oexists2 @o@ (ofun x => ovar f @o@ ovar x @o@ ovar y) @o@ ovar m)
  |}.

Lemma flipLeftAdj {A} `{OType A} (x: A) (y: Flip A) :
  flip x <o= y <-> unflip y <o= x.
Proof.
  destruct y; simpl; reflexivity.
Qed.

Lemma flipRightAdj {A} `{OType A} (x: Flip A) (y: A) :
  x <o= flip y <-> y <o= unflip x.
Proof.
  destruct x; simpl; reflexivity.
Qed.

Lemma flipAdjEq {A} `{OType A} (x: A) (y: Flip A) :
  flip x =o= y <-> x =o= unflip y.
Proof.
  destruct y; simpl. split; intro e; destruct e; split; assumption.
Qed.

Instance Monad_DownSet : Monad DownSet.
Proof.
  constructor; intros; apply funOExt; intro celem; apply funOExt.
  { intro y; simpl; split.
    - intros [ z pf1 pf2 ]. rewrite <- pf2. assumption.
    - intro H. exists (ofun_app x celem); [ assumption | reflexivity ]. }
  { intro x; simpl; split.
    - intros [ z pf1 pf2 ]. rewrite <- flipLeftAdj in pf1.
      rewrite <- pf1. assumption.
    - intro. exists (unflip x); [ reflexivity | ]. destruct x; assumption. }
  { intro c; simpl; split.
    - intros [ b pf_bc [ a pf_ab pf_a ] ].
      exists a; [ exists b | ]; assumption.
    - intros [ a [ b pf_bc pf_ab ] pf_a ].
      exists b; [ | exists a ]; assumption. }
Qed.


Instance MonadBottomOps_DownSet : MonadBottomOps DownSet :=
  {| bottomM := fun _ _ => oexpr (ofun b => oFalse) |}.

Instance MonadBottom_DownSet : MonadBottom DownSet.
Proof.
  constructor; [ typeclasses eauto | ].
  intros. intros a1 a2 Ra a3 a4 R34 pf_false. destruct pf_false.
Qed.


Definition fixDownSet {A B} `{OType A} `{OType B} :
  ((A -o> DownSet B) -o> (A -o> DownSet B)) -o> A -o> DownSet B :=
  oexpr
    (ofun f => ofun a => ofun b =>
     oforall @o@ (ofun g =>
                  oimpl @o@ (oflip (oappr
                                      @o@ oflip' (ovar f @o@ ounequiv (ovar g))
                                      @o@ ounequiv' (ovar g)))
                        @o@ (ounequiv (ovar g) @o@ ovar a @o@ ovar b)
    )).

Instance MonadFixOps_DownSet : MonadFixOps DownSet := {| fixM := @fixDownSet |}.

Instance MonadFix_DownSet : MonadFix DownSet.
Admitted.
