Require Export SepTypes.OrderedType.
Require Export SepTypes.Monad.
Require Export SepTypes.DownSet.
Require Export SepTypes.MonadFix.


(***
 *** Execution Traces
 ***)

(* An execution trace = a list of intermediate states, followed by a final state
if the execution terminated. Note that these are non-empty traces, so that, when
we build sets of traces, non-termination can be represented by the empty set *)
Inductive trace St A : Type :=
| Trace_NonTerm (st:St) : trace St A
| Trace_Term (st:St) (a:A) : trace St A
| Trace_Step (st:St) (tr:trace St A) : trace St A.

Arguments Trace_NonTerm {St A} st.
Arguments Trace_Term {St A} st a.
Arguments Trace_Step {St A} st tr.

(* Non-terminating traces approximate longer traces that are pointwise bigger *)
Inductive traceR St A `{OType St} `{OType A} : trace St A -> trace St A -> Prop :=
| traceR_NonTerm st1 st2 :
    st1 <o= st2 -> traceR St A (Trace_NonTerm st1) (Trace_NonTerm st2)
| traceR_Term st1 st2 a1 a2 :
    st1 <o= st2 -> a1 <o= a2 ->
    traceR St A (Trace_Term st1 a1) (Trace_Term st2 a2)
| traceR_Step st1 st2 tr1 tr2 :
    st1 <o= st2 -> traceR St A tr1 tr2 ->
    traceR St A (Trace_Step st1 tr1) (Trace_Step st2 tr2)
| traceR_NonTerm_step (tr:trace St A) st1 st2 :
    st1 <o= st2 -> traceR St A (Trace_NonTerm st1) (Trace_Step st2 tr)
.

Instance OTtrace St A `{OType St} `{OType A} : OType (trace St A) :=
  {| oleq := traceR St A |}.
Proof.
  constructor.
  { intro tr; induction tr; try constructor; try reflexivity. assumption. }
  { intros tr1 tr2 tr3 R12; revert tr3; induction R12;
      intros tr3 R23; inversion R23;
        constructor; try (etransitivity; eassumption).
    apply IHR12. assumption. }
Defined.


Instance Proper_Trace_NonTerm St A `{OType St} `{OType A} :
  Proper (oleq ==> oleq) (@Trace_NonTerm St A).
Proof.
  intros st1 st2 Rst; constructor; assumption.
Qed.

Instance Proper_Trace_Term St A `{OType St} `{OType A} :
  Proper (oleq ==> oleq ==> oleq) (@Trace_Term St A).
Proof.
  intros st1 st2 Rst a1 a2 Ra; constructor; assumption.
Qed.

Instance Proper_Trace_Step St A `{OType St} `{OType A} :
  Proper (oleq ==> oleq ==> oleq) (@Trace_Step St A).
Proof.
  intros st1 st2 Rst tr1 tr2 Rtr; constructor; assumption.
Qed.


Definition traceNonTerm_ofun {St A} `{OType St} `{OType A}
  : St -o> trace St A :=
  {| ofun_app := Trace_NonTerm |}.

Definition otraceNonTerm {ctx St A} `{OType St} `{OType A} :
  OExpr ctx (St -o> trace St A) := oconst traceNonTerm_ofun.


Program Definition traceTerm_ofun {St A} `{OType St} `{OType A} :
  St -o> A -o> trace St A :=
  {| ofun_app := fun st => {| ofun_app := Trace_Term st |} |}.
Next Obligation. apply Proper_Trace_Term; reflexivity. Defined.
Next Obligation. apply Proper_Trace_Term; reflexivity. Defined.

Definition otraceTerm {ctx St A} `{OType St} `{OType A} :
  OExpr ctx (St -o> A -o> trace St A) := oconst traceTerm_ofun.


Program Definition traceStep_ofun {St A} `{OType St} `{OType A} :
  St -o> trace St A -o> trace St A :=
  {| ofun_app := fun st => {| ofun_app := Trace_Step st |} |}.
Next Obligation. apply Proper_Trace_Step; reflexivity. Defined.
Next Obligation. apply Proper_Trace_Step; reflexivity. Defined.

Definition otraceStep {ctx St A} `{OType St} `{OType A} :
  OExpr ctx (St -o> trace St A -o> trace St A) := oconst traceStep_ofun.


(* Construct the trace that extends tr with (f fin) if tr terminates in state
fin *)
Fixpoint trace_bind {St A B} `{OType St} `{OType A} `{OType B} (tr: trace St A)
         (f: A -o> St -o> trace St B) : trace St B :=
  match tr with
  | Trace_NonTerm st => Trace_NonTerm st
  | Trace_Term st a => ofun_app (ofun_app f a) st
  | Trace_Step st tr' => Trace_Step st (trace_bind tr' f)
  end.

Instance Proper_trace_bind {St A B} `{OType St} `{OType A} `{OType B} :
  Proper (oleq ==> oleq ==> oleq) (@trace_bind St A B _ _ _).
Proof.
  intros tr1 tr2 Rtr; induction Rtr; intros f1 f2 Rf; simpl.
  - constructor; assumption.
  - apply Rf; assumption.
  - constructor; [ | apply IHRtr ]; assumption.
  - constructor; assumption.
Qed.

Program Definition traceBind_ofun {St A B} `{OType St} `{OType A} `{OType B} :
  trace St A -o> (A -o> St -o> trace St B) -o> trace St B :=
  {| ofun_app := fun tr => {| ofun_app := trace_bind tr |} |}.
Next Obligation. apply Proper_trace_bind; reflexivity. Defined.
Next Obligation. apply Proper_trace_bind; reflexivity. Defined.

Definition otraceBind {ctx St A B} `{OType St} `{OType A} `{OType B} :
  OExpr ctx (trace St A -o> (A -o> St -o> trace St B) -o> trace St B) :=
  oconst traceBind_ofun.

(* Construct the set of all traces that extend tr with a trace in (f fin) if tr
terminates in state fin *)
Fixpoint trace_bindM {St A B} `{OType St} `{OType A} `{OType B} (tr: trace St A)
  : (A -o> St -o> DownSet (trace St B)) -o> DownSet (trace St B) :=
  match tr with
  | Trace_NonTerm st =>
    oexpr (ofun f => oreturn @o@ (otraceNonTerm @o@ oconst st))
  | Trace_Term st a =>
    oexpr (ofun f => f @o@ oconst a @o@ oconst st)
  | Trace_Step st tr' =>
    oexpr
      (ofun f =>
       ounion @o@ (oreturn @o@ (otraceNonTerm @o@ oconst st))
              @o@ (obind @o@ (oconst (trace_bindM tr') @o@ f)
                         @o@ (ofun tr'' =>
                              oreturn @o@ (otraceStep @o@ oconst st @o@ tr''))))
  end.

Arguments trace_bindM {_ _ _ _ _ _} tr : simpl nomatch.

Instance Proper_trace_bindM {St A B} `{OType St} `{OType A} `{OType B} :
  Proper (oleq ==> oleq) (@trace_bindM St A B _ _ _).
Proof.
  intros tr1 tr2 Rtr; induction Rtr; simpl; apply Proper_oexpr.
  { apply mkLamExt_leq. rewrite H2. reflexivity. }
  { apply mkLamExt_leq. rewrite H2. rewrite H3. reflexivity. }
  { apply mkLamExt_leq. rewrite H2. f_equiv. rewrite IHRtr. f_equiv.
    apply mkLamExt_leq. rewrite H2. reflexivity. }
  { apply mkLamExt_leq. etransitivity; [ | apply ounion_leq1 ].
    rewrite H2. reflexivity. }
Qed.

Definition traceBindM_ofun {St A B} `{OType St} `{OType A} `{OType B} :
  trace St A -o> (A -o> St -o> DownSet (trace St B)) -o> DownSet (trace St B) :=
  {| ofun_app := trace_bindM |}.

Definition otraceBindM {ctx St A B} `{OType St} `{OType A} `{OType B} :
  OExpr ctx (trace St A -o> (A -o> St -o> DownSet (trace St B)) -o>
             DownSet (trace St B)) :=
  oconst traceBindM_ofun.

(* FIXME: laws for otraceBind, otraceTerm, and otraceStep *)


(***
 *** The Trace Monad = Final Algebra of Sets of Traces
 ***)

(* A trace computation starts from any given input state, and generates a trace
of intermediate states followed by an optional final state (if it terminates) *)
Definition TraceM St `{OType St} A `{OType A} := St -o> DownSet (trace St A).

Instance OTypeF_TraceM St `{OType St} : OTypeF (TraceM St) := fun _ _ => _.

Instance MonadOps_TraceM St `{OType St} : MonadOps (TraceM St) :=
  {| returnM :=
       fun _ _ =>
         oexpr (ofun x => ofun st =>
                oreturn @o@ (otraceTerm @o@ ovar st @o@ ovar x));
     bindM :=
       fun _ _ _ _ =>
         oexpr (ofun m => ofun f => ofun st =>
                obind @o@ (ovar m @o@ ovar st) @o@
                      (ofun tr => otraceBindM @o@ ovar tr @o@ ovar f))
 |}.


(* FIXME HERE: move this to OExpr! *)
Lemma oconst_oexpr {ctx A} `{OType A} (e: OExpr CNil A) res
      {ext: ExtendsTo CNil ctx}
      {w: WeakensTo e (PreExtendsToBase ext) res} :
  oconst (oexpr e) =o= res.
Admitted.

Lemma monad_returnM_bindM {ctx A B} `{OType A} `{OType B} {M} `{Monad M}
      (f: OExpr ctx (A -o> M B _)) x :
  oconst bindM @o@ (oconst returnM @o@ x) @o@ f =o= f @o@ x.
apply monad_return_bind.
Qed.

Lemma monad_bindM_returnM {ctx A} `{OType A} {M} `{Monad M} (m: OExpr ctx (M A _)) :
  oconst bindM @o@ m @o@ oconst returnM =o= m.
apply monad_bind_return.
Qed.

Instance Monad_TraceM St `{OType St} : Monad (TraceM St).
Proof.
  constructor; intros; apply ofunExt; intro.
  { unfold obind, oreturn, bindM, returnM, MonadOps_TraceM.
    rewrite oconst_oexpr; [ | typeclasses eauto ].
    obeta. obeta. obeta.
    rewrite oconst_oexpr; [ | typeclasses eauto ]. obeta. obeta.
    rewrite monad_returnM_bindM. obeta.
    apply funOExt; intro celem. reflexivity. }
  { unfold obind, oreturn, bindM, returnM, MonadOps_TraceM.
    rewrite oconst_oexpr; [ | typeclasses eauto ].
    rewrite oconst_oexpr; [ | typeclasses eauto ].
    obeta. obeta. obeta.
    transitivity (oconst bindM @o@ (m @o@ arg) @o@ oconst returnM);
      [ | rewrite monad_bindM_returnM; reflexivity ].
    f_equiv. apply ofunExt; intro. obeta.
    admit. (* FIXME: need to prove properties of trace_bindM *)
  }
  {
    admit.
  }
Admitted.
