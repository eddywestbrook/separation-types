Require Export SepTypes.OrderedType.
Require Export SepTypes.OFuns.


(***
 *** Ordered Type Contexts
 ***)

(* A context here is just a list of type expressions *)
Inductive Ctx : Type :=
| CNil
| CCons (ctx:Ctx) A {RA:OType A}
.

Notation "ctx :> A" := (CCons ctx A) (left associativity, at level 50).

(* An element of a context is a nested tuple of elements of its types *)
Fixpoint CtxElem (ctx:Ctx) : Type :=
  match ctx with
  | CNil => unit
  | ctx' :> A => CtxElem ctx' * A
  end.

(* OTRelation instance for any CtxElem type *)
Instance OType_CtxElem ctx : OType (CtxElem ctx).
Proof.
  induction ctx; typeclasses eauto.
Defined.

(* Typeclasses Transparent OType_CtxElem. *)

(*
Definition ctxHead ctx : Type :=
  match ctx with
  | CNil => unit
  | CCons _ A => A
  end.

Instance OType_ctxHead ctx : OType (ctxHead ctx) :=
  match ctx with
  | CNil => OTunit
  | @CCons _ _ RA => RA
  end.

Definition ctxTail ctx :=
  match ctx with
  | CNil => CNil
  | ctx' :> _ => ctx'
  end.
*)


(***
 *** Ordered Expressions and Variables
 ***)

(* An ordered expression in ctx is just a Proper function from ctx *)
Definition OExpr ctx A `{OType A} : Type := CtxElem ctx -o> A.

Arguments OExpr ctx A {_} : simpl never.

(* Low-level lambda (we use "ofun", below, to give a nice high-level lambda) *)
(* Notation "'olambda' e" := (ofun_curry e) (at level 99, right associativity). *)

Inductive OVar : Ctx -> forall A `{OType A}, Type :=
| OVar_0 {ctx A} `{OType A} : OVar (ctx :> A) A
| OVar_S {ctx B A} `{OType A} `{OType B} (v: OVar ctx A) : OVar (ctx :> B) A
.

(* The last-bound variable in a context *)
Definition var_top {ctx A} `{OType A} : OExpr (ctx :> A) A := snd_ofun.

(* Weaken an OExpr by adding a type to the context *)
Definition weaken1 {ctx A B} `{OType A} `{OType B}
           (e: OExpr ctx A) : OExpr (ctx :> B) A :=
  compose_ofun fst_ofun e.

Fixpoint varSemantics {ctx A} `{OType A} (v:OVar ctx A) : OExpr ctx A :=
  match v in OVar ctx' A' return OExpr ctx' A' with
  | OVar_0 => var_top
  | OVar_S v => weaken1 (varSemantics v)
  end.

Coercion varSemantics : OVar >-> OExpr.


(***
 *** Notation for Application
 ***)

(* FIXME: weaken both sides to a join of their respective contexts! *)
Definition oexpr_apply {ctx A B} `{OType A} `{OType B}
           (f: OExpr ctx (A -o> B)) (g: OExpr ctx A) : OExpr ctx B :=
  ofun_apply f g.

Instance Proper_oexpr_apply {ctx A B} `{OType A} `{OType B} :
  Proper (oleq ==> oleq ==> oleq) (@oexpr_apply ctx A B _ _).
Proof.
  intros f1 f2 Rf g1 g2 Rg. rewrite Rf. rewrite Rg. reflexivity.
Qed.

(* Application *)
Notation "x @o@ y" :=
  (oexpr_apply x y) (left associativity, at level 20).


(***
 *** Notation for Variables, Lambdas, and Top-level Expressions
 ***)

(* Build an A from an OExpr in unit context of type A *)
Definition oexpr {A} `{OType A} (e: OExpr CNil A) : A := ofun_app e tt.
Arguments oexpr {_ _} e : simpl never.

Instance Proper_oexpr {A} `{OType A} : Proper (oleq ==> oleq) (@oexpr A _).
Proof.
  intros c1 c2 Rc. apply Rc. reflexivity.
Qed.

(* Build an OExpr from a constant *)
Definition oconst {ctx A} `{OType A} (a:A) : OExpr ctx A :=
  const_ofun a.

Instance Proper_oconst {ctx A} `{OType A} :
  Proper (oleq ==> oleq) (@oconst ctx A _).
Proof.
  intros a1 a2 Ra c1 c2 Rc. simpl. assumption.
Qed.

(* Helper function to build lambdas *)
(*
Definition mkLam {ctx A B} `{OType A} `{OType B}
           (body : (forall {ctx'} `{WeakensTo (ctx :> A) ctx'}, OVar ctx' A) ->
                   OExpr (ctx :> A) B) :
  OExpr ctx (A -o> B) :=
  ofun_curry (body (fun _ _ => weakenVar OVar_0)).
 *)

(*
Definition mkLam {ctx A B} `{OType A} `{OType B}
           (body : OVar (ctx :> A) A -> OExpr (ctx :> A) B) :
  OExpr ctx (A -o> B) := ofun_curry (body OVar_0).
 *)

Definition mkLam {ctx A B} `{OType A} `{OType B}
           (body : OExpr (ctx :> A) A -> OExpr (ctx :> A) B) :
  OExpr ctx (A -o> B) := ofun_curry (body var_top).

Notation "'ofun' x => e" :=
  (mkLam (fun x => e))
    (right associativity, at level 99).

Notation "'ofun' ( x : A ) => e" :=
  (mkLam (fun (x : OExpr _ A) => e))
    (right associativity, at level 99, x at level 0).


(***
 *** Weakening
 ***)

(* Inductive proof that ctx1 can be extended to ctx2 *)
Inductive extendsTo ctx1 : Ctx -> Type :=
| ExtendsRefl : extendsTo ctx1 ctx1
| ExtendsCons {ctx2} (ext: extendsTo ctx1 ctx2) A `{OType A}  :
    extendsTo ctx1 (ctx2 :> A)
.

Arguments ExtendsRefl {_}.
Arguments ExtendsCons {_ _} ext A {_}.

(* Typeclass version of the above *)
Class ExtendsTo ctx1 ctx2 : Type :=
  extendsProof : extendsTo ctx1 ctx2.

Instance ExtendsToRefl ctx : ExtendsTo ctx ctx := ExtendsRefl.

Instance ExtendsToCons {ctx1 ctx2} (ext: ExtendsTo ctx1 ctx2) A `{OType A} :
  ExtendsTo ctx1 (ctx2 :> A) :=
  ExtendsCons ext A.

(* Weaken a context by mapping backwards from the weaker to the stronger one *)
Fixpoint weakenContext {ctx1 ctx2} (ext: extendsTo ctx1 ctx2) :
  CtxElem ctx2 -o> CtxElem ctx1 :=
  match ext in extendsTo _ ctx2 return CtxElem ctx2 -o> CtxElem ctx1 with
  | ExtendsRefl => id_ofun
  | ExtendsCons ext' _ => compose_ofun fst_ofun (weakenContext ext')
  end.

(* Weakening for OExprs *)
Definition weakenExpr {ctx1 ctx2} `{ext: ExtendsTo ctx1 ctx2} {A} `{OType A}
           (e: OExpr ctx1 A) : OExpr ctx2 A :=
  compose_ofun (weakenContext ext) e.

Instance Proper_weakenExpr {ctx1 ctx2} `{ext: ExtendsTo ctx1 ctx2} {A} `{OType A} :
  Proper (oleq ==> oleq) (weakenExpr (ext:=ext) (A:=A)).
Proof.
  intros e1 e2 Re. apply Proper_compose_ofun; [ reflexivity | assumption ].
Qed.

Lemma weakenExpr_App {ctx1 ctx2} (ext: ExtendsTo ctx1 ctx2)
      {A B} `{OType A} `{OType B} (e1: OExpr ctx1 (A -o> B)) (e2: OExpr ctx1 A) :
  weakenExpr (e1 @o@ e2) =o= weakenExpr e1 @o@ weakenExpr e2.
  unfold weakenExpr, oexpr_apply. rewrite compose_ofun_apply.
  reflexivity.
Qed.


(* Weakening for variables *)
Fixpoint weakenVar_h {ctx1 ctx2} (ext: extendsTo ctx1 ctx2) :
  forall {A} `{OType A}, OVar ctx1 A -> OVar ctx2 A :=
  match ext in extendsTo _ ctx2
        return forall {A} `{OType A}, OVar ctx1 A -> OVar ctx2 A
  with
  | ExtendsRefl => fun _ _ v => v
  | ExtendsCons ext' _ => fun _ _ v => OVar_S (weakenVar_h ext' v)
  end.

Definition weakenVar {ctx1 ctx2} `{ext:ExtendsTo ctx1 ctx2} {A} `{OType A}
           (v:OVar ctx1 A) : OVar ctx2 A :=
  weakenVar_h ext v.

(* Weakening is the same whether we do it before or after varSemantics *)
Lemma weakenVar_weakenExpr {ctx1 ctx2} `{ext:ExtendsTo ctx1 ctx2} {A} `{OType A}
      (v:OVar ctx1 A) : weakenExpr (ext:=ext) v =o= weakenVar v.
Proof.
  revert v; induction ext; intro v; simpl.
  { apply id_compose_ofun. }
  { unfold weaken1. rewrite <- IHext. unfold weakenExpr. simpl.
    rewrite compose_compose_ofun. reflexivity. }
Qed.


(* Convert a "variable" (an OExpr in a shorter context) into an expression in
the current context *)
Definition ovar {ctx A} `{OType A} {ctx'} `{ext:ExtendsTo ctx ctx'}
           (e:OExpr ctx A) : OExpr ctx' A := weakenExpr e.


(***
 *** Substitution
 ***)

Inductive CtxSubst : Ctx -> Ctx -> Type :=
| CtxSubstBase {ctx A} `{OType A} (e: OExpr ctx A) : CtxSubst (ctx :> A) ctx
| CtxSubstCons {ctx1 ctx2} (s: CtxSubst ctx1 ctx2) A `{OType A} :
    CtxSubst (ctx1 :> A) (ctx2 :> A)
.

(* Use a substitution like a mapping *)
Fixpoint substContext {ctx1 ctx2} (s: CtxSubst ctx1 ctx2)
  : CtxElem ctx2 -o> CtxElem ctx1 :=
  match s in CtxSubst ctx1 ctx2
        return CtxElem ctx2 -o> CtxElem ctx1
  with
  | CtxSubstBase e => pair_ofun id_ofun e
  | CtxSubstCons s' _ =>
    pair_ofun (compose_ofun fst_ofun (substContext s')) snd_ofun
  end.

Definition substExpr {ctx1 ctx2 A} `{OType A} (e: OExpr ctx1 A)
           (s: CtxSubst ctx1 ctx2) : OExpr ctx2 A :=
  compose_ofun (substContext s) e.


(***
 *** Typeclasses for Weakening
 ***)

Inductive PreExtendsTo : Ctx -> Ctx -> Type :=
| PreExtendsToBase {ctx1 ctx2} (ext: extendsTo ctx1 ctx2) :
    PreExtendsTo ctx1 ctx2
| PreExtendsToCons {ctx1 ctx2} (pext: PreExtendsTo ctx1 ctx2) A `{OType A} :
    PreExtendsTo (ctx1 :> A) (ctx2 :> A)
.

Fixpoint weakenPreContext {ctx1 ctx2} (pext: PreExtendsTo ctx1 ctx2) :
  CtxElem ctx2 -o> CtxElem ctx1 :=
  match pext in PreExtendsTo ctx1 ctx2 return CtxElem ctx2 -o> CtxElem ctx1 with
  | PreExtendsToBase ext => weakenContext ext
  | PreExtendsToCons pext' _ =>
    pair_ofun (compose_ofun fst_ofun (weakenPreContext pext')) snd_ofun
  end.

Class WeakensTo {ctx ctx_e A} `{OType A} (e: OExpr ctx_e A)
      (pext: PreExtendsTo ctx_e ctx) (res: OExpr ctx A) :=
  weakensTo :
    compose_ofun (weakenPreContext pext) e =o= res.

Instance WeakensTo_Const {ctx ctx_e A} `{OType A}
         (a:A) (pext: PreExtendsTo ctx_e ctx) :
  WeakensTo (oconst a) pext (oconst a).
Proof.
  apply funOExt; intro celem. reflexivity.
Qed.

Instance WeakensTo_Refl {ctx A} `{OType A} (e: OExpr ctx A) :
  WeakensTo e (PreExtendsToBase (ExtendsToRefl ctx)) e.
Proof.
  apply id_compose_ofun.
Qed.

Instance WeakensTo_Trivial {ctx_e ctx A} `{OType A} (e: OExpr ctx_e A)
         (ext: ExtendsTo ctx_e ctx) :
  WeakensTo e (PreExtendsToBase ext) (ovar e) | 10.
Proof.
  apply id_compose_ofun.
Qed.

Instance WeakensTo_App {ctx_e ctx A B} `{OType A} `{OType B}
         (e1: OExpr ctx_e (A -o> B)) e2
         (pext: PreExtendsTo ctx_e ctx) res1 res2 :
  WeakensTo e1 pext res1 -> WeakensTo e2 pext res2 ->
  WeakensTo (e1 @o@ e2) pext (res1 @o@ res2).
Proof.
  unfold WeakensTo. intros. rewrite <- H1. rewrite <- H2.
  unfold oexpr_apply. rewrite compose_ofun_apply.
  reflexivity.
Qed.

Instance WeakensTo_Lam {ctx_e ctx A B} `{OType A} `{OType B}
         (body: OExpr (ctx_e :> A) A -> OExpr (ctx_e :> A) B)
         (pext: PreExtendsTo ctx_e ctx) body_res :
  (forall v v_res,
      WeakensTo v (PreExtendsToCons pext A) v_res ->
      WeakensTo (body v) (PreExtendsToCons pext A) (body_res v_res)) ->
  WeakensTo (mkLam body) pext (mkLam body_res).
Proof.
  unfold WeakensTo, mkLam.
  intro pf. rewrite <- (pf var_top var_top).
  { rewrite compose_ofun_curry. reflexivity. }
  { simpl. apply compose_pair_snd. }
Qed.


Class WeakensToVar {ctx_e ctx_e_res ctx ctx_res A} `{OType A}
      (e: OExpr ctx_e A) (ext_v: ExtendsTo ctx_e ctx)
      (pext: PreExtendsTo ctx ctx_res)
      (res: OExpr ctx_e_res A) (ext_res: ExtendsTo ctx_e_res ctx_res) :=
  weakensToVar :
    compose_ofun (weakenPreContext pext) (ovar e) =o= (ovar res).

Instance WeakensToVar_Refl {ctx_e ctx A} `{OType A}
         (e: OExpr ctx_e A) (pext: PreExtendsTo ctx_e ctx) res :
  WeakensTo e pext res ->
  WeakensToVar e (ExtendsToRefl _) pext res (ExtendsToRefl _).
Proof.
  intro pf; apply pf.
Qed.

Instance WeakensToVar_Const {ctx_e ctx A} `{OType A}
         (e: OExpr ctx_e A) (ext_v: ExtendsTo ctx_e ctx) :
  WeakensToVar e ext_v (PreExtendsToBase (ExtendsToRefl _)) e ext_v.
Proof.
  apply id_compose_ofun.
Qed.

Instance WeakensToVar_Cons1 {ctx_e ctx ctx_res ctx_e_res A B} `{OType A} `{OType B}
         (e: OExpr ctx_e A) (ext_v: ExtendsTo ctx_e ctx)
         (pext: PreExtendsTo ctx ctx_res)
         (res: OExpr ctx_e_res A) (ext_res : ExtendsTo ctx_e_res ctx_res) :
  WeakensToVar e ext_v pext res ext_res ->
  WeakensToVar e (ExtendsToCons ext_v B)
               (PreExtendsToCons pext B) res (ExtendsToCons ext_res B).
Proof.
  unfold WeakensToVar, ovar, ovar, weakenExpr. simpl.
  intro pf. repeat rewrite <- compose_compose_ofun. rewrite <- pf.
  apply funOExt; intro celem. reflexivity.
Qed.

Instance WeakensToVar_Cons2 {ctx_e ctx ctx_res ctx_e_res A B} `{OType A} `{OType B}
         (e: OExpr ctx_e A) (ext_v: ExtendsTo ctx_e ctx)
         (ext: ExtendsTo ctx ctx_res)
         (res: OExpr ctx_e_res A) (ext_res : ExtendsTo ctx_e_res ctx_res) :
  WeakensToVar e ext_v (PreExtendsToBase ext) res ext_res ->
  WeakensToVar e ext_v (PreExtendsToBase (ExtendsToCons ext B))
               res (ExtendsToCons ext_res B).
Proof.
  unfold WeakensToVar, ovar, ovar, weakenExpr. simpl.
  intro pf. repeat rewrite <- compose_compose_ofun. rewrite <- pf.
  apply funOExt; intro celem. reflexivity.
Qed.


Instance WeakensTo_Var {ctx_e ctx ctx_e_res ctx_res A} `{OType A}
         (e: OExpr ctx_e A) (ext_v: ExtendsTo ctx_e ctx)
         (pext: PreExtendsTo ctx ctx_res)
         (res: OExpr ctx_e_res A) (ext_res: ExtendsTo ctx_e_res ctx_res) :
  WeakensToVar e ext_v pext res ext_res ->
  WeakensTo (ovar e) pext (ovar res).
Proof.
  intro pf; apply pf.
Qed.


(***
 *** Typeclasses for Substitution
 ***)

Class SubstsTo {ctx ctx_res A} `{OType A} (e: OExpr ctx A)
      (s: CtxSubst ctx ctx_res) res :=
  substsTo : substExpr e s =o= res.

Instance SubstsTo_Const {ctx ctx_res A} `{OType A} (a:A)
         (s: CtxSubst ctx ctx_res) :
  SubstsTo (oconst a) s (oconst a).
Proof.
  apply funOExt; intro celem. reflexivity.
Qed.

Instance SubstsTo_App {ctx ctx_res A B} `{OType A} `{OType B}
         (e1: OExpr ctx (A -o> B)) (e2: OExpr ctx A)
         (s: CtxSubst ctx ctx_res) res1 res2 :
  SubstsTo e1 s res1 -> SubstsTo e2 s res2 ->
  SubstsTo (e1 @o@ e2) s (res1 @o@ res2).
Proof.
  unfold SubstsTo. unfold substExpr. intros. rewrite <- H1. rewrite <- H2.
  unfold oexpr_apply. rewrite compose_ofun_apply.
  reflexivity.
Qed.

Instance SubstsTo_Lam {ctx ctx_res A B} `{OType A} `{OType B}
         (body: OExpr (ctx :> A) A -> OExpr (ctx :> A) B)
         (s: CtxSubst ctx ctx_res)
         (body_res: OExpr (ctx_res :> A) A -> OExpr (ctx_res :> A) B) :
  (forall v v_res,
      SubstsTo v (CtxSubstCons s A) v_res ->
      SubstsTo (body v) (CtxSubstCons s A) (body_res v_res)) ->
  SubstsTo (mkLam body) s (mkLam body_res).
Proof.
  unfold SubstsTo, substExpr, mkLam. intro pf. rewrite <- (pf var_top var_top).
  { rewrite compose_ofun_curry. reflexivity. }
  { simpl. apply compose_pair_snd. }
Qed.

Class SubstsToVar {ctx ctx_e ctx_res ctx_e_res A} `{OType A}
      (e: OExpr ctx_e A) (ext: ExtendsTo ctx_e ctx)
      (s: CtxSubst ctx ctx_res) (res: OExpr ctx_e_res A)
      (ext_res: ExtendsTo ctx_e_res ctx_res) :=
  substsToVar : substExpr (ovar (ext:=ext) e) s =o= ovar (ext:=ext_res) res.

Instance SubstsToVar_Refl {ctx ctx_res A} `{OType A}
         (e: OExpr ctx A) (s: CtxSubst ctx ctx_res) res :
  SubstsTo e s res -> SubstsToVar e (ExtendsToRefl ctx) s res (ExtendsToRefl _).
Proof.
  unfold SubstsTo, SubstsToVar, ovar, ExtendsToRefl, substExpr, weakenExpr.
  simpl. repeat rewrite id_compose_ofun. intro; assumption.
Qed.

Instance SubstsToVar_VarSubst {ctx A} `{OType A} (e_subst: OExpr ctx A) :
  SubstsToVar var_top (ExtendsToRefl _) (CtxSubstBase e_subst)
              e_subst (ExtendsToRefl _).
Proof.
  unfold SubstsTo, SubstsToVar, ovar, var_top.
  unfold substExpr, weakenExpr, ExtendsToRefl.
  simpl. repeat rewrite id_compose_ofun. rewrite compose_pair_snd.
  reflexivity.
Qed.

Instance SubstsToVar_Const {ctx ctx_e A B} `{OType A} `{OType B}
         (e: OExpr ctx_e A) (ext: ExtendsTo ctx_e ctx)
         (e_subst: OExpr ctx B) :
  SubstsToVar e (ExtendsToCons ext B) (CtxSubstBase e_subst) e ext.
Proof.
  unfold SubstsTo, SubstsToVar, ovar, weakenExpr, substExpr. simpl.
  apply funOExt; intro celem. reflexivity.
Qed.

Instance SubstsToVar_Cons {ctx_e ctx_e_res ctx ctx_res A B} `{OType A} `{OType B}
         (e: OExpr ctx_e A) (ext: ExtendsTo ctx_e ctx)
         (s: CtxSubst ctx ctx_res) (res: OExpr ctx_e_res A) ext_res :
  SubstsToVar e ext s res ext_res ->
  SubstsToVar e (ExtendsToCons ext B) (CtxSubstCons s B)
              res (ExtendsToCons ext_res B).
Proof.
  unfold SubstsTo, SubstsToVar, ovar, ovar, weakenExpr, substExpr. simpl.
  intro pf. repeat rewrite <- compose_compose_ofun. rewrite <- pf.
  apply funOExt; intro celem. reflexivity.
Qed.

Instance SubstsTo_Var {ctx ctx_res ctx_e ctx_e_res A} `{OType A}
         (e: OExpr ctx_e A) (ext: ExtendsTo ctx_e ctx)
         (s: CtxSubst ctx ctx_res)
         (res: OExpr ctx_e_res A) (ext_res: ExtendsTo ctx_e_res ctx_res)
         (res_w: OExpr ctx_res A) :
  SubstsToVar e ext s res ext_res ->
  WeakensTo res (PreExtendsToBase ext_res) res_w ->
  SubstsTo (ovar (ext:=ext) e) s res_w.
Proof.
  unfold SubstsTo, SubstsToVar, WeakensTo. intros.
  etransitivity; eassumption.
Qed.


(***
 *** Beta and Eta Rules for OFuns
 ***)

Lemma ofunEta {ctx A B} `{OType A} `{OType B} (e: OExpr ctx (A -o> B)) :
  (ofun x => ovar e @o@ ovar x) =o= e.
Proof.
  apply funOExt; intro celem. apply funOExt; intro a. reflexivity.
Qed.

Lemma ofunExt {ctx A B} `{OType A} `{OType B} (e1 e2: OExpr ctx (A -o> B))
      (pf: forall arg, e1 @o@ arg =o= e2 @o@ arg) :
  e1 =o= e2.
Proof.
  apply funOExt; intro celem. unfold oexpr_apply in pf.
  apply funOExt; intro a. revert celem.
  rewrite <- (funOExt _ _ (e1 @o@ oconst a) (e2 @o@ oconst a)).
  apply pf.
Qed.

Lemma ofunExt_leq {ctx A B} `{OType A} `{OType B} (e1 e2 : OExpr ctx (A -o> B))
      (pf: forall arg, e1 @o@ arg <o= e2 @o@ arg) :
  e1 <o= e2.
Proof.
  intros c1 c2 Rc a1 a2 Ra. rewrite Rc; rewrite Ra.
  apply (pf (oconst a2)). reflexivity.
Qed.

Lemma ofunEta' {ctx A B} `{OType A} `{OType B} (e: OExpr ctx (A -o> B)) :
  (ofun x => ovar e @o@ x) =o= e.
Proof.
  apply funOExt; intro celem. apply funOExt; intro a. reflexivity.
Qed.

Lemma mkLamExt {ctx A B} `{OType A} `{OType B}
      (body1 body2: OExpr (ctx :> A) A -> OExpr (ctx :> A) B) :
  body1 var_top =o= body2 var_top -> mkLam body1 =o= mkLam body2.
Proof.
  intro pf. apply funOExt; intro celem. unfold mkLam. rewrite pf. reflexivity.
Qed.

Lemma mkLamExt_leq {ctx A B} `{OType A} `{OType B}
      (body1 body2: OExpr (ctx :> A) A -> OExpr (ctx :> A) B) :
  body1 var_top <o= body2 var_top -> mkLam body1 <o= mkLam body2.
Proof.
  intro pf. intros c1 c2 Rc; rewrite Rc. unfold mkLam. rewrite pf. reflexivity.
Qed.

Lemma ofunBeta {ctx A B} `{OType A} `{OType B}
      (body: OExpr (ctx :> A) A -> OExpr (ctx :> A) B) (arg: OExpr ctx A) res
      {st:
         forall v, SubstsTo v (CtxSubstBase arg) arg ->
                   SubstsTo (body v) (CtxSubstBase arg) res} :
  (mkLam body) @o@ arg =o= res.
Proof.
  unfold SubstsTo in st. rewrite <- (st var_top).
  { unfold substExpr, mkLam, oexpr_apply. simpl.
    rewrite ofun_apply_ofun_curry. reflexivity. }
  { apply compose_pair_snd. }
Qed.

Ltac obeta := rewrite ofunBeta; [ | typeclasses eauto ].


(***
 *** Tests for the obeta Tactic
 ***)
Lemma beta_test {ctx A} `{OType A} (e: OExpr ctx A) :
  (ofun x => ovar x) @o@ e =o= e.
  obeta. reflexivity.
Qed.

Lemma beta_test2 {ctx A B} `{OType A} `{OType B} (e: OExpr ctx (A -o> B)) :
  (ofun f => (ofun x => ovar f @o@ ovar x)) @o@ e =o= e.
  obeta. apply ofunExt; intro. obeta. reflexivity.
Qed.


(***
 *** Ordered Expressions for Unit
 ***)

Definition ott {ctx} : OExpr ctx unit := oconst tt.

Lemma ott_terminal {ctx} (e: OExpr ctx unit) : e =o= ott.
Proof.
  apply funOExt; intro c. destruct (e @@ c). reflexivity.
Qed.


(***
 *** Ordered Expressions for Pairs
 ***)

Definition opair {ctx A B} `{OType A} `{OType B} : OExpr ctx (A -o> B -o> A*B) :=
  oconst (ofun_curry id_ofun).
Definition ofst {ctx A B} `{OType A} `{OType B} : OExpr ctx (A * B -o> A) :=
  oconst fst_ofun.
Definition osnd {ctx A B} `{OType A} `{OType B} : OExpr ctx (A * B -o> B) :=
  oconst snd_ofun.

Notation "( x ,o, y )" := (opair @o@ x @o@ y : OExpr _ _) (at level 0).

Lemma ofst_opair {ctx A B} `{OType A} `{OType B}
      (e1: OExpr ctx A) (e2: OExpr ctx B) :
  ofst @o@ (e1 ,o, e2) =o= e1.
Proof.
  apply funOExt; intro c. reflexivity.
Qed.

Lemma osnd_opair {ctx A B} `{OType A} `{OType B}
      (e1: OExpr ctx A) (e2: OExpr ctx B) :
  osnd @o@ (e1 ,o, e2) =o= e2.
Proof.
  apply funOExt; intro c. reflexivity.
Qed.

Lemma opair_ext {ctx A B} `{OType A} `{OType B} (e: OExpr ctx (A*B)) :
  opair @o@ (ofst @o@ e) @o@ (osnd @o@ e) =o= e.
Proof.
  apply funOExt; intro c. simpl. destruct (ofun_app e c). reflexivity.
Qed.


(***
 *** Ordered Expressions for Sums
 ***)

Definition oinl {ctx A B} `{OType A} `{OType B} : OExpr ctx (A -o> A + B) :=
  oconst inl_ofun.
Definition oinr {ctx A B} `{OType A} `{OType B} : OExpr ctx (B -o> A + B) :=
  oconst inr_ofun.
Definition osumElim {ctx A B C} `{OType A} `{OType B} `{OType C} :
  OExpr ctx ((A -o> C) -o> (B -o> C) -o> A + B -o> C) :=
  oconst sum_elim_ofun.

Lemma osumElim_oinl {ctx A B C} `{OType A} `{OType B} `{OType C}
      (f1 : OExpr ctx (A -o> C)) (f2 : OExpr ctx (B -o> C)) e :
  osumElim @o@ f1 @o@ f2 @o@ (oinl @o@ e) =o= f1 @o@ e.
Proof.
  apply funOExt; intro c. reflexivity.
Qed.

Lemma osumElim_oinr {ctx A B C} `{OType A} `{OType B} `{OType C}
      (f1 : OExpr ctx (A -o> C)) (f2 : OExpr ctx (B -o> C)) e :
  osumElim @o@ f1 @o@ f2 @o@ (oinr @o@ e) =o= f2 @o@ e.
Proof.
  apply funOExt; intro c. reflexivity.
Qed.


(***
 *** Ordered Expressions for Propositions
 ***)

Definition oTrue {ctx} : OExpr ctx Prop := oconst True.
Definition oFalse {ctx} : OExpr ctx Prop := oconst False.

Definition oforall {ctx A} `{OType A} : OExpr ctx ((A -o> Prop) -o> Prop) :=
  oconst forall_ofun.
Definition oexists {ctx A} `{OType A} : OExpr ctx ((A -o> Prop) -o> Prop) :=
  oconst exists_ofun.
Definition oexists2 {ctx A} `{OType A} :
  OExpr ctx ((A -o> Prop) -o> (Flip A -o> Prop) -o> Prop) :=
  oconst exists2flip_ofun.

Definition oand {ctx} : OExpr ctx (Prop -o> Prop -o> Prop) :=
  oconst and_ofun.
Definition oor {ctx} : OExpr ctx (Prop -o> Prop -o> Prop) :=
  oconst or_ofun.
Definition oimpl {ctx} : OExpr ctx (Flip Prop -o> Prop -o> Prop) :=
  oconst impl_ofun.
Definition oappr {ctx A} `{OType A} : OExpr ctx (Flip A -o> A -o> Prop) :=
  oconst oleq_ofun.


Lemma oor_leq1 {ctx} (P Q: OExpr ctx Prop) : P <o= oor @o@ P @o@ Q.
Proof.
  intros c1 c2 Rc; rewrite Rc. intro pf; left; assumption.
Qed.

Lemma oor_leq2 {ctx} (P Q: OExpr ctx Prop) : Q <o= oor @o@ P @o@ Q.
Proof.
  intros c1 c2 Rc; rewrite Rc. intro pf; right; assumption.
Qed.

Lemma oor_lub {ctx} (P Q R: OExpr ctx Prop) :
  (P <o= R) -> (Q <o= R) -> oor @o@ P @o@ Q <o= R.
Proof.
  intros RPR RQR c1 c2 Rc; rewrite Rc. intro pf.
  destruct pf; [ apply (RPR c2) | apply (RQR c2) ]; try assumption; reflexivity.
Qed.


Lemma oand_leq1 {ctx} (P Q: OExpr ctx Prop) : oand @o@ P @o@ Q <o= P.
Proof.
  intros c1 c2 Rc; rewrite Rc. intro pf; destruct pf; assumption.
Qed.

Lemma oand_leq2 {ctx} (P Q: OExpr ctx Prop) : oand @o@ P @o@ Q <o= Q.
Proof.
  intros c1 c2 Rc; rewrite Rc. intro pf; destruct pf; assumption.
Qed.

Lemma oand_glb {ctx} (P Q R: OExpr ctx Prop) :
  (P <o= Q) -> (P <o= R) -> P <o= oand @o@ Q @o@ R.
Proof.
  intros RPQ RPR c1 c2 Rc; rewrite Rc. intro pf.
  split; [ apply (RPQ c2) | apply (RPR c2) ]; try assumption; reflexivity.
Qed.


(***
 *** Flip and Equiv Types
 ***)

Fixpoint flipCtx (ctx : Ctx) :=
  match ctx with
  | CNil => CNil
  | ctx' :> A => flipCtx ctx' :> Flip A
  end.

Fixpoint flipCtxElem {ctx} : CtxElem ctx -> CtxElem (flipCtx ctx) :=
  match ctx return CtxElem ctx -> CtxElem (flipCtx ctx) with
  | CNil => fun celem => celem
  | ctx' :> A => fun celem => (flipCtxElem (fst celem), flip (snd celem))
  end.

Instance Proper_flipCtxElem ctx : Proper (oleq --> oleq) (@flipCtxElem ctx).
Proof.
  induction ctx; intros c1 c2 Rc.
  - destruct c1; destruct c2; reflexivity.
  - destruct Rc. split; [ apply IHctx | ]; assumption.
Qed.

Fixpoint unflipCtxElem {ctx} : CtxElem (flipCtx ctx) -> CtxElem ctx :=
  match ctx return CtxElem (flipCtx ctx) -> CtxElem ctx with
  | CNil => fun celem => celem
  | ctx' :> A => fun celem => (unflipCtxElem (fst celem), unflip (snd celem))
  end.

Instance Proper_unflipCtxElem ctx : Proper (oleq --> oleq) (@unflipCtxElem ctx).
Proof.
  induction ctx; intros c1 c2 Rc.
  - destruct c1; destruct c2; reflexivity.
  - destruct Rc. split; [ apply IHctx | ]; assumption.
Qed.

Lemma flipCtxElem_unflipCtxElem ctx (celem: CtxElem ctx) :
  unflipCtxElem (flipCtxElem celem) =o= celem.
Proof.
  revert celem; induction ctx; intros; [ reflexivity | ].
  destruct celem. destruct (IHctx c).
  split; split; try reflexivity; assumption.
Qed.

Lemma unflipCtxElem_flipCtxElem ctx (celem: CtxElem (flipCtx ctx)) :
  flipCtxElem (unflipCtxElem celem) =o= celem.
Proof.
  revert celem; induction ctx; intros; [ reflexivity | ].
  destruct celem. destruct (IHctx c). simpl. rewrite flip_unflip.
  split; split; try reflexivity; assumption.
Qed.


(* A "flipped" ordered expression *)
Definition OExprFlip ctx A `{OType A} : Type := OExpr (flipCtx ctx) A.

Arguments OExprFlip ctx A {_} : simpl never.

Program Definition oflip {ctx A} `{OType A} (e: OExprFlip ctx A)
  : OExpr ctx (Flip A) :=
  {| ofun_app := fun celem => flip (e @@ flipCtxElem celem) |}.
Next Obligation.
  intros c1 c2 Rc. simpl. rewrite Rc. reflexivity.
Defined.

Program Definition ounflip {ctx A} `{OType A} (e: OExpr ctx (Flip A))
  : OExprFlip ctx A :=
  {| ofun_app := fun celem => unflip (e @@ unflipCtxElem celem) |}.
Next Obligation.
  intros c1 c2 Rc. simpl. rewrite Rc. reflexivity.
Defined.

Lemma oflip_ounflip {ctx A} `{OType A} (e: OExprFlip ctx A) :
  ounflip (oflip e) =o= e.
  revert e; induction ctx; intros; apply funOExt; intro c; [ reflexivity | ].
  simpl. rewrite flip_unflip. rewrite unflipCtxElem_flipCtxElem.
  destruct c; reflexivity.
Qed.

Lemma ounflip_oflip {ctx A} `{OType A} (e: OExpr ctx (Flip A)) :
  oflip (ounflip e) =o= e.
  revert e; induction ctx; intros; apply funOExt; intros c; simpl;
    rewrite flip_unflip; [ reflexivity | ].
  rewrite flipCtxElem_unflipCtxElem. destruct c; reflexivity.
Qed.

Program Definition oflip' {ctx A} `{OType A} (e: OExpr ctx A)
  : OExprFlip ctx (Flip A) :=
  {| ofun_app := fun celem => flip (e @@ unflipCtxElem celem) |}.
Next Obligation.
  intros c1 c2 Rc. simpl. rewrite Rc. reflexivity.
Defined.

Program Definition ounflip' {ctx A} `{OType A} (e: OExprFlip ctx (Flip A))
  : OExpr ctx A :=
  {| ofun_app := fun celem => unflip (e @@ flipCtxElem celem) |}.
Next Obligation.
  intros c1 c2 Rc. simpl. rewrite Rc. reflexivity.
Defined.

Lemma oflip'_ounflip' {ctx A} `{OType A} (e: OExpr ctx A) :
  ounflip' (oflip' e) =o= e.
  revert e; induction ctx; intros; apply funOExt; intro c; [ reflexivity | ].
  simpl. rewrite flipCtxElem_unflipCtxElem.
  destruct c; reflexivity.
Qed.

Lemma ounflip'_oflip' {ctx A} `{OType A} (e: OExprFlip ctx (Flip A)) :
  oflip' (ounflip' e) =o= e.
  revert e; induction ctx; intros; apply funOExt; intros c; simpl;
    rewrite flip_unflip; [ reflexivity | ].
  rewrite unflipCtxElem_flipCtxElem. rewrite flip_unflip.
  destruct c; reflexivity.
Qed.


Definition ounequiv {ctx A} `{OType A} (e : OExpr ctx (Equiv A)) :
  OExpr ctx A :=
  compose_ofun e unequiv_ofun.

Program Definition ounequiv' {ctx A} `{OType A} (e : OExpr ctx (Equiv A)) :
  OExprFlip ctx A :=
  ounflip (compose_ofun e unequiv'_ofun).
