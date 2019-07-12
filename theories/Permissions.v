Require Export SepTypes.OrderedType.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Relations.Relation_Operators.
Require Export Coq.Classes.RelationClasses.

Record perm (A:Type) `{OType A} : Type :=
  {
    view : A -> A -> Prop;  (* PER over configs *)
    view_Proper :> Proper (oleq ==> oleq ==> oleq) view;
    view_PER :> PER view;
    upd  : A -> A -> Prop;  (* allowed transitions *)
    upd_Proper :> Proper (oleq ==> oleq ==> oleq) upd;
    upd_PO :> PreOrder upd;
  }.

Arguments view {_ _} p.
Arguments upd {_ _} p.

Instance PER_view A `{OType A} p : PER (view p) := view_PER A p.
Instance PreOrder_upd A `{OType A} p : PreOrder (upd p) := upd_PO A p.

Instance Proper_view `{OType} (p:perm A) :
  Proper (oleq ==> oleq ==> oleq) (view p) :=
  view_Proper _ p.

Instance Proper_upd `{OType} (p:perm A) :
  Proper (oleq ==> oleq ==> oleq) (upd p) :=
  upd_Proper _ p.

Program Instance OType_perm A `{OType A} : OType (perm A) :=
  {| oleq :=
       fun p q =>
         forall x y,
           (view q) x y <o= (view p) x y /\ (upd p) x y <o= (upd q) x y;
  |}.
Next Obligation.
  constructor.
  - intros p x y; split; reflexivity.
  - intros p1 p2 p3 leq12 leq23 x y; destruct (leq12 x y); destruct (leq23 x y).
    split; etransitivity; eassumption.
Defined.


Program Definition meet_perm `{OType} (Ps: perm A -> Prop) : perm A :=
  {|
    view := clos_trans _ (fun x y => exists2 p, Ps p & view p x y);
    upd  := fun x y => forall p, Ps p -> upd p x y
  |}.
Next Obligation.
  intros x1 x2 leq_x y1 y2 leq_y in_vew_trans. revert x2 y2 leq_x leq_y.
  induction in_vew_trans; intros.
  - destruct H0. apply t_step. exists x0; try assumption.
    rewrite <- leq_x. rewrite <- leq_y. assumption.
  - eapply t_trans.
    + apply IHin_vew_trans1; [ assumption | reflexivity ].
    + apply IHin_vew_trans2; [ reflexivity | assumption ].
Defined.
Next Obligation.
  constructor.
  - intros x y r_xy; induction r_xy.
    + destruct H0. apply t_step. exists x0; [ | symmetry ]; assumption.
    + eapply t_trans; eassumption.
  - intros x y z r_xy r_yz. eapply t_trans; eassumption.
Defined.
Next Obligation.
  intros x1 x2 leq_x y1 y2 leq_y in_upd p in_p.
  rewrite <- leq_x. rewrite <- leq_y. apply in_upd. assumption.
Defined.
Next Obligation.


(* FIXME HERE:
+ prove that meet_perm is a glb
+ define top and bottom perms
+ define sep_at
+ prove sep_at_anti_monotone
+ prove bottom is separate from everything (that is valid)
+ define separating conjunction
+ prove sep_conj bottom p = p
+ prove sep_conj is Proper
+ define Perms as upwards-closed sets
+ define singleton Perms as the upward closure of a single perm
+ define meet on Perms
+ prove that Perms_meet is a glb
+ Define binary meet as a special case
+ Define conjunction of Perms pointwise
+ Define the top and bottom Perms sets
+ Define entailment as the inverse of lte_Perms
+ Define impl_Perms as the adjoint (w.r.t. entailment) of conjunction
*)