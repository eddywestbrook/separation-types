Require Export SepTypes.OrderedType.
Require Export SepTypes.Monad.
Require Export SepTypes.MonadFix.


(***
 *** Execution Traces
 ***)

(* An execution trace = a list of intermediate states, followed by a final state
if the execution terminated *)
Inductive trace St A : Type :=
| Trace_NonTerm : trace St A
| Trace_Term (st:St) (a:A) : trace St A
| Trace_Step (st:St) (tr:trace St A) : trace St A.

Arguments Trace_NonTerm {St A}.
Arguments Trace_Term {St A} st a.
Arguments Trace_Step {St A} st tr.

(* Non-terminating traces approximate longer traces that are pointwise bigger *)
Inductive traceR St A `{OType St} `{OType A} : trace St A -> trace St A -> Prop :=
| traceR_NonTerm (tr:trace St A) : traceR St A Trace_NonTerm tr
| traceR_Term st1 st2 a1 a2 :
    st1 <o= st2 -> a1 <o= a2 ->
    traceR St A (Trace_Term st1 a1) (Trace_Term st2 a2)
| traceR_Step st1 st2 tr1 tr2 :
    st1 <o= st2 -> traceR St A tr1 tr2 ->
    traceR St A (Trace_Step st1 tr1) (Trace_Step st2 tr2)
.

Instance OTtrace St A `{OType St} `{OType A} : OType (trace St A) :=
  {| oleq := traceR St A |}.
Proof.
  constructor.
  { intro tr. induction tr; constructor; try reflexivity. assumption. }
  { intros tr1 tr2 tr3 R12; revert tr3; induction R12; intros tr3 R23.
    - constructor.
    - inversion R23.
      constructor; try assumption; etransitivity; eassumption.
    - inversion R23. constructor; [ etransitivity; eassumption | ].
      apply IHR12; assumption. }
Defined.

Instance Proper_Trace_Term St A `{OType St} `{OType A} :
  Proper (oleq ==> oleq ==> oleq) (@Trace_Term St A).
Proof.
  intros st1 st2 Rst a1 a2 Ra; constructor; assumption.
Qed.

Program Definition traceTerm_ofun {St A} `{OType St} `{OType A} :
  St -o> A -o> trace St A :=
  {| ofun_app := fun st => {| ofun_app := Trace_Term st |} |}.
Next Obligation. apply Proper_Trace_Term; reflexivity. Defined.
Next Obligation. apply Proper_Trace_Term; reflexivity. Defined.

Definition otraceTerm {ctx St A} `{OType St} `{OType A} :
  OExpr ctx (St -o> A -o> trace St A) := const_ofun traceTerm_ofun.


Instance Proper_Trace_Step St A `{OType St} `{OType A} :
  Proper (oleq ==> oleq ==> oleq) (@Trace_Step St A).
Proof.
  intros st1 st2 Rst tr1 tr2 Rtr; constructor; assumption.
Qed.

Program Definition traceStep_ofun {St A} `{OType St} `{OType A} :
  St -o> trace St A -o> trace St A :=
  {| ofun_app := fun st => {| ofun_app := Trace_Step st |} |}.
Next Obligation. apply Proper_Trace_Step; reflexivity. Defined.
Next Obligation. apply Proper_Trace_Step; reflexivity. Defined.

Definition otraceStep {ctx St A} `{OType St} `{OType A} :
  OExpr ctx (St -o> trace St A -o> trace St A) := const_ofun traceStep_ofun.


(* Construct the trace that extends tr with (f fin) if tr terminates in state
fin *)
Fixpoint trace_bind {St A B} `{OType St} `{OType A} `{OType B} (tr: trace St A)
         (f: A -o> St -o> trace St B) : trace St B :=
  match tr with
  | Trace_NonTerm => Trace_NonTerm
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
Qed.

Program Definition traceBind_ofun {St A B} `{OType St} `{OType A} `{OType B} :
  trace St A -o> (A -o> St -o> trace St B) -o> trace St B :=
  {| ofun_app := fun tr => {| ofun_app := trace_bind tr |} |}.
Next Obligation. apply Proper_trace_bind; reflexivity. Defined.
Next Obligation. apply Proper_trace_bind; reflexivity. Defined.

Definition otraceBind {ctx St A B} `{OType St} `{OType A} `{OType B} :
  OExpr ctx (trace St A -o> (A -o> St -o> trace St B) -o> trace St B) :=
  const_ofun traceBind_ofun.


(* Construct the set of all traces that extend tr with a trace in (f fin) if tr
terminates in state fin *)
Fixpoint trace_bindM {St A B} `{OType St} `{OType A} `{OType B}
         (tr: trace St A) (f: A -o> St -o> FixM (trace St B)) : FixM (trace St B) :=
  match tr with
  | Trace_NonTerm => 
  | Trace_Term st a => ofun_app (ofun_app f a) st
  | Trace_Step st tr' =>
    ofun_app (ofun_app bindM (trace_bindM tr' f))
             (compose_ofun (ofun_app traceStep_ofun st) returnM)
  end.

Instance Proper_trace_bindM {St A B} `{OType St} `{OType A} `{OType B} :
  Proper (oleq ==> oleq ==> oleq) (@trace_bindM St A B _ _ _).
Proof.
  intros tr1 tr2 Rtr; induction Rtr; intros f1 f2 Rf.
  { induction tr; simpl; intros; intro.
    - inversion H3. rewrite <- H5 in H2. inversion H2. constructor.
    - 
    
 intro; intros. simpl. intro.
inversion H3. rewrite <- H5 in H2. inversion H2. destruct a2.
    simpl in H7; rewrite <- H7.
apply traceR_NonTerm.
 simpl; intros; intro.
  { 
*)

(* FIXME: laws for otraceBind, otraceTerm, and otraceStep *)


(***
 *** The Trace Monad = Final Algebra of Sets of Traces
 ***)

(* A trace computation starts from any given input state, and generates a trace
of intermediate states followed by an optional final state (if it terminates) *)
Definition TraceM St `{OType St} A `{OType A} := St -o> FixM (trace St A).

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
                      (ofun tr => ofun b =>
                       otraceBind 
)
)
 |}.


         (* For each input st, return x as the output and st as the final state,
         with no intermediate states *)
         lambdaDownSet (fun st => downClose ([], Some (x, st)));
     bindM :=
       fun _ _ _ _ m f =>
         (* For each input state st... *)
         lambdaDownSet
           (fun st =>
              bindDownSet
                (* Pass st into m *)
                (applyDownSet m st)
                (fun trace_out1 =>
                   (* Get (trace1, out) = (m st), and test if out is a Some *)
                   optElim
                     (fun a_st1 =>
                        (* If (m st) = (trace1, Some (a, st2)), then get
                           (trace2, out) = (f a st), and return the result
                           (trace1 ++ trace2, out) *)
                        mapDownSet
                          (fun trace_out2 =>
                             (fst trace_out1 ++ fst trace_out2, snd trace_out2))
                          (applyDownSet (f (fst a_st1)) (snd a_st1)))
                     (* Otherwise, m did not terminate, so we don't call f at
                     all, and just return (trace1, None) *)
                     (downClose (fst trace_out1, None))
                     (* (snd trace_out1) is the option output of (m st) *)
                     (snd trace_out1)))
  |}.

Instance Monad_TraceM St `{OType St} : Monad (TraceM St).
Proof.
  constructor.
  { intros. intros a1 a2 Ra. simpl. apply Proper_lambdaDownSet. intro st.
    rewrite Ra. reflexivity. }
  { intros. intros m1 m2 Rm f1 f2 Rf. apply Proper_lambdaDownSet. intro st.
    rewrite Rm. apply Proper_bindDownSet; try reflexivity. intro trace_out1.
    apply (Proper_optElim_eq _ _); try reflexivity.
    intro a_st1. apply Proper_bindDownSet; try reflexivity.
    apply Proper_applyDownSet; [ apply Rf | reflexivity ]. }
  { intros. simpl.
    rewrite <- (downSetEta (f a)).
    apply Proper_lambdaDownSet_equiv. apply funOExt; intro st.
    rewrite downSetBeta; [ | intros st1 st2 Rst; rewrite Rst; reflexivity ].
    rewrite DownSet_return_bind.
    - simpl. unfold mapDownSet.
      etransitivity; [ | apply DownSet_bind_return ].
      apply Proper_bindDownSet_equiv; try reflexivity.
      apply funOExt. intros [ tr ret ]. reflexivity.
    - intros tr_out1 tr_out2 Rtr_out.
      eapply Proper_optElim; try (rewrite Rtr_out; reflexivity).
      intros a_st1 a_st1' Ra_st1.
      apply Proper_bindDownSet; [ rewrite Ra_st1; reflexivity | ].
      intro f_tr_out. rewrite Rtr_out. reflexivity. }
  { intros. simpl. rewrite <- (downSetEta m).
    apply Proper_lambdaDownSet_equiv. apply funOExt; intro st.
    etransitivity; [ | apply DownSet_bind_return ].
    f_equiv. apply funOExt. intros [ tr [[ a st'] | ]]; [ | reflexivity ].
    simpl. unfold mapDownSet. rewrite downSetBeta.
    - rewrite DownSet_return_bind; [ simpl; rewrite app_nil_r; reflexivity | ].
      intros tr_ret1 tr_ret2 Rtr_ret. rewrite Rtr_ret. reflexivity.
    - intros st1 st2 Rst. rewrite Rst. reflexivity. }
  { intros.
