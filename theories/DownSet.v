Require Export SepTypes.OrderedType.
Require Export SepTypes.MonadFix.


(***
 *** The Downward-Closed Sets as a Monad
 ***)

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


(***
 *** Set Operations
 ***)

(* Binary union *)
Definition ounion {ctx A} `{OType A}
  : OExpr ctx (DownSet A -o> DownSet A -o> DownSet A) :=
  ofun s1 => ofun s2 => ofun a =>
  oor @o@ (ovar s1 @o@ ovar a) @o@ (ovar s2 @o@ ovar a).

(* Binary intersection *)
Definition ointersect {ctx A} `{OType A}
  : OExpr ctx (DownSet A -o> DownSet A -o> DownSet A) :=
  ofun s1 => ofun s2 => ofun a =>
  oand @o@ (ovar s1 @o@ ovar a) @o@ (ovar s2 @o@ ovar a).

(* The complete set *)
Definition ocomplete {ctx A} `{OType A} : OExpr ctx (DownSet A) :=
  ofun a => oTrue.

(* The empty set *)
Definition oempty {ctx A} `{OType A} : OExpr ctx (DownSet A) :=
  ofun a => oFalse.


(***
 *** The Fixed-Point Operations
 ***)

Instance MonadBottomOps_DownSet : MonadBottomOps DownSet :=
  {| bottomM := fun _ _ => oexpr oempty |}.

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
