(** Ported E 3.5.9 heuristics as explicit worker strategies (plan M09 Stage A).

    A heuristic replaces, for one engine, the production clause selection (Passive), literal
    selection and KBO instance, and runs the given-clause loop "lean": without the Focus, Goal and
    Consumer producers, which have no E counterpart. Every inference is still an ordinary
    certificate step (resolution, factoring, equality resolution, paramodulation), so a heuristic
    never changes what the kernel accepts. Symbol-introducing features (splitting with fresh
    definitions, definitions) stay off. SInE axiom filtering ([sine_filter]) exists only in the
    evaluation members [c18csl], [sat001sl] and [c18sl], so no strategy of the default portfolio
    filters axioms; the evaluation variants [e208av]/[y1346av] add the engine's AVATAR splitting
    (its existing certificate path) and [e208sl] reads SInE levels only to order its queues.
    Parameters come from HEURISTICS/schedule.vars. A heuristic with [vampire] set ([of_vampire])
    runs a ported Vampire slice on the same loop instead ([Vampire]); its preprocessing (function
    definition elimination, equality resolution with deletion), forward literal rewriting and unit
    resulting resolution are ordinary certificate steps too. *)

open Evaluation

type t = {
  name : string;
  e_name : string;  (** The E heuristic this ports. *)
  order : Eorder.t;
  selection : Eselection.t;
  queues : Evaluation.queue list;
  ordered_rewriting : bool;
      (** E forward_demod 2: also rewrite with instances of unorientable unit equations that
          decrease in KBO. forward_demod 1 is the production (orientable rules only). *)
  destructive_er : destructive;
  avatar : bool;
      (** AVATAR splitting. Off in every ported strategy: E's split_clauses 0, and the LPO ports'
          split_clauses 4 (negative clauses only, with E's split predicates) is not ported. On in
          the evaluation variants [e208av] and [y1346av] ({!with_avatar}). *)
  unfold : int option;
      (** The strategy's equational-definition unfolding ([Strategy.t.unfold], [Unfold]). E's
          eqdef_incrlimit is 20 in all three schedule entries, and all three use it. [y1346]
          unfolds: on its loop, which follows E's, unfolding is E's own search, and it solved more
          of the problems that E solves with y1346 within 3x E's given count and lost none. On
          {!loop_ported} unfolding solved more of the development corpus's problems that have a
          definition but lost two of them in every seed, so its derived evaluation variants [y1346k]
          and [y1346av] and the LPO ports ([h042], [h047b31]), which run that loop, keep [None] as
          measured, although E's entries also say 20; [x1276] unfolds, with E's loop details. *)
  prefer_initial : bool;
      (** E's prefer_initial_clauses: every queue selects the initial clauses first
          ({!Evaluation.evaluate}). *)
  sine_filter : (float * int) option;
      (** E's SInE axiom filter (CONTROL/cco_sine.c, GSinE with CountFormulas):
          [Some (benevolence, depth)] inserts only the axioms that the negated-conjecture axioms
          reach within [depth] trigger steps, a symbol triggering an axiom when it occurs in at most
          [benevolence] times as many axioms as the axiom's least frequent symbol ({!Sine_levels}
          with generality 0, E's unlimited generosity). An evaluation member's incompleteness only:
          the others, production included, never filter, so the portfolio stays refutationally
          complete. *)
  tptp_sos : bool;
      (** E's use_tptp_sos: the set of support is the clauses of TPTP role conjecture instead of the
          clauses without a positive literal (che_clausesets.c ClauseSetMarkSOS). *)
  loop : loop;
      (** Which parts of E's given-clause loop the lean worker follows beyond the shared lean loop
          ({!loop_e}); [loop_ported] keeps the measured search of the members ported first. *)
  vampire : Vampire.t option;
      (** A ported Vampire slice ({!of_vampire}): its symbol precedence, KBO weights, literal order
          and literal selection, and its age and weight queues (Vampire's AWPassiveClauseContainer)
          replace [order], [selection] and the queue mix. *)
}

and loop = {
  uniq_order : bool;
      (** E's evaluation order of the initial clauses (cco_proofproc.c ProofStateInit): ascending
          Uniqweight (che_clauseweight.c UniqWeightCompute), ties in input order, instead of the
          input order. The evaluation order is the FIFO weight and every queue's tie-break. *)
  full_rewrite : bool;
      (** E's rewrite levels: the selected clause (ProcessClause's ForwardContractClause) and an
          active clause rewritten by a new unit (insert_new_clauses, CPIsIRVictim) are rewritten
          with FullRewrite, i.e. also with the decreasing instances of unorientable unit equations,
          while a new clause uses the strategy's forward_demod ([ordered_rewriting]). *)
  at_once : bool;
      (** A given clause simplified at selection is processed in the same selection, as E's
          ProcessClause does (the engine's [given_at_once]). *)
  e_calculus : bool;
      (** E's generating inferences (cco_proofproc.c ProcessClause, generate_new_clauses): the given
          clause joins the active set (and backward-rewrites the active clauses) before its
          inferences, so its own conclusions are rewritten with it when admitted; a unit given
          resolves with the active clauses only, as every given does (production also resolves it
          with Passive); two equational literals are never resolved (E reaches such conclusions by
          superposition and equality resolution); and equality resolution and factoring of a clause
          run when it is selected, not when it is admitted, without negative factoring. *)
  discount : bool;
      (** E's DISCOUNT loop (cco_proofproc.c insert_new_clauses, ProcessClause): a new clause is
          only rewritten, destructively equality-resolved and unit-simplified with the active
          clauses; Passive clauses neither simplify nor subsume, duplicates and subsumed clauses
          wait for their selection, where the given clause is contracted with the active clauses
          (rewriting, unit and contextual simplify-reflect, subsumption), and every given
          backward-subsumes the active clauses. *)
  duplicates : bool;
      (** With [discount]: a variant of a retained clause also waits for its selection (E has no
          duplicate deletion; the copy is subsumed when selected and takes that turn). Off, the
          DISCOUNT admission still drops variants at emission, as {!loop_ported} does. *)
  orphans : bool;
      (** With [discount]: a Passive orphan (a premise of its generating inference was retired by
          backward simplification) is dropped when it would be selected (E's ClauseIsOrphaned). *)
  presat : bool;
      (** E's presaturation interreduction (presat_interreduction, PROVER/eprover.c run_saturation):
          the loop first runs without generating inferences until Passive is empty, then every
          active clause returns to Passive, re-evaluated as a processed clause in E's set order
          (oriented positive units, unorientable positive units, negative units, the rest), and
          equal evaluations are ordered by evaluation order (E's eval_count) from then on. *)
  presat_duplicates : bool;
      (** With [discount] and [presat]: while presaturation interreduction runs, variants stay in
          Passive until their selection whatever [duplicates] says, and the given clause's
          replacement is checked against the active clauses only (E's ForwardContractClause subsumes
          with the processed set, never with the unprocessed one). No generating inference runs
          there, so these variants are E's own: the copies that rewriting and unit simplification
          make. The selection that discards one (the copy is subsumed then) is one of E's selection
          turns, so the queue schedule stays E's. *)
  resolved : bool;
      (** E's ClauseRemoveSuperfluousLiterals (EqnListRemoveResolved) at every ForwardModifyClause:
          a negative literal whose two sides are the same term is removed when the clause is
          admitted or selected (an equality resolution with the empty substitution), not only by a
          generating equality resolution when the clause is processed. *)
  cp_initial : bool;
      (** E's CPInitial: a clause that rewriting, unit deletion or subsumption resolution changed is
          no longer initial (ccl_rewrite.c:1406, ccl_subsumption.c:1310, ccl_context_sr.c:89), which
          moves it out of SimulateSOS's normal priority unless it is in the set of support and
          decides prefer_initial_clauses; destructive equality resolution keeps the flag. Off, every
          replacement inherits it. *)
  gen_order : bool;
      (** With [e_calculus]: a given clause's conclusions are emitted in E's creation order
          ({!E_genorder}): the equality factors, the equality resolvents, then the paramodulants
          (resolvents included) with the given as the from clause, then those with the given as the
          into clause, each over the given's positions in reverse of E's collection order and the
          partners in E's FP7 index order. E evaluates them in that order, and its evaluation
          counter breaks the ties between equal evaluations. Off, they are emitted as the inference
          cursors produce them. *)
  backward : bool;
      (** With [discount]: E's backward simplification by a given clause (cco_proofproc.c
          ProcessClause): the processed clauses it rewrites, then those it subsumes, then those a
          unit given simplifies (eliminate_unit_simplified_clauses: a negative unit cuts the
          matching positive literal of an all-positive processed clause, an unorientable positive
          unit equation the matching negative literal of a processed clause with one), which leave
          the processed set and come back, simplified, as new clauses. Off, the given backward-
          subsumes first and simplifies no processed clause but by rewriting. *)
  lit_order : bool;
      (** E's literal order ({!Eselection.e_rank}: ForwardContractClause sorts a non-unit given
          clause before selecting its literals): the selection functions take the first of equally
          good literals in that order, and [gen_order] visits the given's literals in it. Off, the
          clause's own (sorted) literal order decides. *)
  replacing : bool;
      (** With [discount]: E's timing of destructive equality resolution and of
          prefer_initial_clauses (cco_proofproc.c). The initial clauses are inserted without
          ForwardModifyClause (ProofStateInit), so destructive equality resolution reaches an
          initial clause when it is selected; a selected clause is destructively equality-resolved
          after its contraction, and the replacement is a processed clause that waits in Passive
          (replacing_inferences); prefer_initial_clauses raises priorities only while the initial
          clauses are inserted. Off, destructive equality resolution also runs when a clause is
          admitted and first when it is selected, and prefer_initial_clauses holds for every initial
          clause. On in {!loop_e} (the members on E's loop), off in {!loop_member}. *)
  sim_paramod : bool;
      (** With [gen_order]: E's simultaneous paramodulation (pm_type ParamodSim, which every ported
          strategy's E entry sets; ccl_paramod.c ClauseSimParamodConstruct). A paramodulant replaces
          every occurrence of the into subterm in the into clause (every literal, both sides), not
          only the one at the inference's position, and with the given clause as the from clause
          there is one conclusion per from position, into clause and into subterm, made at the first
          eligible position in E's order (cco_paramodulation.c compute_into_pm_pos_clause). The
          further replacements are ordinary Paramodulate steps into proof-only intermediates
          ({!E_simparamod}), so the certificate format and the kernel are unchanged. Off, every
          eligible position gives its own conclusion with one replacement. *)
  top_once : bool;
      (** With [gen_order]: E makes a superposition between two positive literals at the top of both
          once, with the given clause as the from clause (cco_paramodulation.c
          ComputeFromParamodulants skips the into positions at the top of a positive literal of the
          given: "Positive/positive top level has already been done in the into-case"). Off, the
          given as the into clause meets such a partner at the top too, which repeats that
          conclusion (up to the orientation of its equation). *)
  eqn_subsume : bool;
      (** With [discount]: E's equational unit subsumption (ccl_subsumption.c
          UnitClauseSubsumesClause, eqn_subsumes_termpair). A positive unit equation [l = r]
          subsumes a clause with a positive literal [s = t] whose sides agree except at one
          position, where they are an instance of [l] and [r] in either order (descending through
          equal heads with exactly one differing argument), not only at the top: E deletes
          [g(f(a,b)) = g(f(b,a))] with [f(X,Y) = f(Y,X)]. Forward (ForwardSubsumption, by the
          processed unorientable unit equations: an oriented one has rewritten such a literal to a
          tautology) when a clause is selected, and backward by a selected unorientable unit
          equation (eliminate_backward_subsumed_clauses). A deletion only; no proof step. *)
}
(** E given-clause loop details that change which clauses a port selects (found by comparing the
    ports' given-clause traces with E's -l1 output). *)

(** E er_varlit_destructive / er_strong_destructive (CONTROL/cco_proofproc.c forward contraction): a
    negative literal x != t, with the variable x not in t, is resolved away and the clause is
    replaced by the result, an ordinary equality-resolution step. [Varlit] requires t to be a
    variable too. *)
and destructive = Er_off | Er_varlit | Er_strong

(** The lean loop of the first E ports, kept as measured for the members that run it. *)
let loop_ported =
  {
    uniq_order = false;
    full_rewrite = false;
    at_once = false;
    e_calculus = false;
    discount = false;
    duplicates = false;
    orphans = false;
    presat = false;
    presat_duplicates = false;
    resolved = false;
    cp_initial = false;
    gen_order = false;
    backward = false;
    lit_order = false;
    replacing = false;
    sim_paramod = false;
    top_once = false;
    eqn_subsume = false;
  }

(** Every E loop detail of {!loop}: those found with E's given-clause traces, E's selection order
    ([gen_order], [lit_order], [backward] and [resolved]), E's simultaneous paramodulation
    ([sim_paramod]), its single top-level overlap of positive literals ([top_once]) and equational
    unit subsumption ([eqn_subsume]). *)
let loop_e =
  {
    uniq_order = true;
    full_rewrite = true;
    at_once = true;
    e_calculus = true;
    discount = true;
    duplicates = true;
    orphans = true;
    presat = false;
    presat_duplicates = true;
    resolved = true;
    cp_initial = true;
    gen_order = true;
    backward = true;
    lit_order = true;
    replacing = true;
    sim_paramod = true;
    top_once = true;
    eqn_subsume = true;
  }

(** The loop details for the strategies whose E entry runs presaturation interreduction: {!loop_e}
    with [presat], without [replacing] (measured without it: the members' solve counts and screens
    with AXIOM_LEAN_LOOP=presat). *)
let loop_presat = { loop_e with presat = true; replacing = false }

(** The loop of the members [y1346] and [sat001] and of the evaluation member [e208e] (fitted to E's
    given-clause traces): E's loop with presaturation interreduction, except that in the main loop a
    variant of a retained clause is still dropped at emission ([duplicates] off; presaturation keeps
    E's variants, [presat_duplicates]) and Passive orphans stay ([orphans] off). Both deviations
    keep selections for clauses E would also process: our per-given cost is far above E's, and on
    the problems that E solves and the members do not, each of the two cost more refutations than it
    gained. [e208] keeps {!loop_ported}: on E's loop it lost more problems of the development corpus
    at 10 s / 1 worker than it gained (its gains come at 30 s / 4 workers), so [e208e] carries E's
    loop for evaluation. *)
let loop_member = { loop_presat with duplicates = false; orphans = false }

(* The loop details by name, for the evaluation override AXIOM_LEAN_LOOP. *)
let loop_fields =
  [
    ("uniq_order", fun l -> { l with uniq_order = true });
    ("full_rewrite", fun l -> { l with full_rewrite = true });
    ("at_once", fun l -> { l with at_once = true });
    ("e_calculus", fun l -> { l with e_calculus = true });
    ("discount", fun l -> { l with discount = true });
    ("duplicates", fun l -> { l with duplicates = true });
    ("orphans", fun l -> { l with orphans = true });
    ("presat", fun l -> { l with presat = true });
    ("presat_duplicates", fun l -> { l with presat_duplicates = true });
    ("resolved", fun l -> { l with resolved = true });
    ("cp_initial", fun l -> { l with cp_initial = true });
    ("gen_order", fun l -> { l with gen_order = true });
    ("lit_order", fun l -> { l with lit_order = true });
    ("backward", fun l -> { l with backward = true });
    ("replacing", fun l -> { l with replacing = true });
    ("sim_paramod", fun l -> { l with sim_paramod = true });
    ("top_once", fun l -> { l with top_once = true });
    ("eqn_subsume", fun l -> { l with eqn_subsume = true });
  ]

(** [ported], [e], [presat] or a comma-separated list of {!loop} field names. *)
let loop_of_string text =
  match String.trim text with
  | "ported" -> loop_ported
  | "e" -> loop_e
  | "presat" -> loop_presat
  | text ->
      List.fold_left
        (fun l name ->
          match List.assoc_opt (String.trim name) loop_fields with
          | Some f -> f l
          | None ->
              invalid_arg
                (Printf.sprintf "unknown loop detail %S (known: ported, e, presat, %s)" name
                   (String.concat ", " (List.map fst loop_fields))))
        loop_ported (String.split_on_char ',' text)

(* (1.ConjectureRelativeSymbolWeight(SimulateSOS,0.5,100,100,100,100,1.5,1.5,1),
    4.ConjectureRelativeSymbolWeight(ConstPrio,0.1,100,100,100,100,1.5,1.5,1.5),
    1.FIFOWeight(PreferProcessed),
    1.ConjectureRelativeSymbolWeight(PreferNonGoals,0.5,100,100,100,100,1.5,1.5,1),
    4.Refinedweight(SimulateSOS,3,2,2,1.5,2)) *)
let crsw conj_multiplier positive =
  Crsw
    {
      conj_multiplier;
      fweight = 100;
      cweight = 100;
      pweight = 100;
      vweight = 100;
      max_term = 1.5;
      max_literal = 1.5;
      positive;
    }

let mix_208 =
  [
    { count = 1; priority = Simulate_sos; weight = crsw 0.5 1. };
    { count = 4; priority = Const_prio; weight = crsw 0.1 1.5 };
    { count = 1; priority = Prefer_processed; weight = Fifo };
    { count = 1; priority = Prefer_non_goals; weight = crsw 0.5 1. };
    {
      count = 4;
      priority = Simulate_sos;
      weight = Refined { fweight = 3; vweight = 2; max_term = 2.; max_literal = 1.5; positive = 2. };
    };
  ]

(** G-E--_208_C12_11_nc_F1_SE_CS_SP_PS_S5PRR_S04BN: KBO6, invfreqhack precedence, precedence weights
    (to_const_weight 0), PSelectComplexExceptUniqMaxHorn, forward_demod 2, forward contextual
    simplify-reflect, destructive ER. Its SAT check (ConjMinMinFreq, 5000 steps) is not ported. *)
let e208 =
  {
    name = "e208";
    e_name = "G-E--_208_C12_11_nc_F1_SE_CS_SP_PS_S5PRR_S04BN";
    order =
      {
        ordering = Kbo;
        precedence = Invfreq_hack;
        weights = Precedence_weights;
        const_weight = 0;
        e_signature = false;
        e_ranks = false;
      };
    selection = P_complex_except_uniq_max_horn;
    queues = mix_208;
    ordered_rewriting = true;
    destructive_er = Er_strong;
    avatar = false;
    unfold = Some Unfold.default_limit;
    prefer_initial = false;
    sine_filter = None;
    tptp_sos = false;
    loop = loop_ported;
    vampire = None;
  }

(** G----_Y1346__C12_02_nc_F1_AE_CS_SP_S2S: KBO6, invfreqhack precedence, aritymax0 weights,
    (20.Diversityweight(ConstPrio,1,1,1.5,1,1,0,0,2,0),5.OrientLMaxWeight(ConstPrio,2,1,2,1,1),
    1.FIFOWeight(ConstPrio)), SelectNewComplexAHP, forward_demod 1, contextual simplify-reflect,
    destructive ER on variable literals. *)
let y1346 =
  {
    name = "y1346";
    e_name = "G----_Y1346__C12_02_nc_F1_AE_CS_SP_S2S";
    order =
      {
        ordering = Kbo;
        precedence = Invfreq_hack;
        weights = Arity_max0;
        const_weight = 0;
        e_signature = false;
        e_ranks = false;
      };
    selection = New_complex_ahp;
    queues =
      [
        {
          count = 20;
          priority = Const_prio;
          weight =
            Diversity
              {
                fweight = 1;
                vweight = 1;
                max_term = 1.5;
                max_literal = 1.;
                positive = 1.;
                fdiff1 = 0.;
                fdiff2 = 0.;
                vdiff1 = 2.;
                vdiff2 = 0.;
              };
        };
        {
          count = 5;
          priority = Const_prio;
          weight =
            Orient_lmax
              { fweight = 2; vweight = 1; unorientable = 2.; max_literal = 1.; positive = 1. };
        };
        { count = 1; priority = Const_prio; weight = Fifo };
      ];
    ordered_rewriting = false;
    destructive_er = Er_varlit;
    avatar = false;
    unfold = Some Unfold.default_limit;
    prefer_initial = false;
    sine_filter = None;
    tptp_sos = false;
    loop = loop_member;
    vampire = None;
  }

(** SAT001_MinMin_p005000_rr_RG: KBO6, invfreq precedence, invfreqrank weights (to_const_weight 1),
    the 208 queue mix, SelectMaxLComplexAvoidPosPred, forward_demod 1 (so strong rhs instantiation
    has no effect), contextual simplify-reflect, destructive ER. Its SAT check is not ported. *)
let sat001 =
  {
    name = "sat001";
    e_name = "SAT001_MinMin_p005000_rr_RG";
    order =
      {
        ordering = Kbo;
        precedence = Invfreq;
        weights = Invfreq_rank;
        const_weight = 1;
        e_signature = false;
        e_ranks = false;
      };
    selection = Max_l_complex_avoid_pos_pred;
    queues = mix_208;
    ordered_rewriting = false;
    destructive_er = Er_strong;
    avatar = false;
    unfold = Some Unfold.default_limit;
    prefer_initial = false;
    sine_filter = None;
    tptp_sos = false;
    loop = loop_member;
    vampire = None;
  }

(** The same heuristic on E's own KBO instance (Eorder [e_signature]): E's internal symbols in the
    generators, generated constant weights for to_const_weight 0, one precedence for predicate and
    function symbols. Checked against E's printed weights and evaluations; the plain names keep the
    first port's instance, which the 30 s / 4 worker measurements used. *)
let e_kbo h =
  { h with name = h.name ^ "k"; order = { h.order with e_signature = true }; loop = loop_ported }

(* E's own instance with E's own first-occurrence tie breaker ({!Eorder.e_pos_ranks}): the KBO of
   the members ported with E's loop details. On REL012-1 the first port's instance orients the meet
   definition against E (1 of 1,221 processed equations), this one as E does. *)
let e_instance (o : Eorder.t) = { o with e_signature = true; e_ranks = true }

(* The OrientLMaxWeight and FIFO tail of the H----_042 / H----_047 queue mixes. *)
let lmax_fifo =
  [
    {
      count = 5;
      priority = Const_prio;
      weight =
        Orient_lmax { fweight = 2; vweight = 1; unorientable = 2.; max_literal = 1.; positive = 1. };
    };
    { count = 1; priority = Const_prio; weight = Fifo };
  ]

(* E's LPO4 instance: to_weight_gen none, E's own first-occurrence tie breaker, and one precedence for predicate and function symbols
   (OCBFunCompare), which [e_signature] selects. *)
let lpo4 precedence =
  {
    Eorder.ordering = Lpo;
    precedence;
    weights = Unit_weights;
    const_weight = 0;
    e_signature = true;
    e_ranks = true;
  }

(** H----_042_B03_F1_AE_Q4_SP_S2S: LPO4 with the invarity precedence,
    (10.Refinedweight(PreferGoals,1,2,2,2,0.5),10.Refinedweight(PreferNonGoals,2,1,2,2,2),
    5.OrientLMaxWeight(ConstPrio,2,1,2,1,1),1.FIFOWeight(ConstPrio)), SelectNewComplexAHP,
    forward_demod 1, destructive ER on variable literals. Not ported: split_clauses 4 (negative
    clauses, E split predicates); forward_context_sr is off in E, while the lean loop keeps the
    standard subsumption resolution. *)
let h042 =
  {
    name = "h042";
    e_name = "H----_042_B03_F1_AE_Q4_SP_S2S";
    order = lpo4 Invarity;
    selection = New_complex_ahp;
    queues =
      [
        {
          count = 10;
          priority = Prefer_goals;
          weight =
            Refined { fweight = 1; vweight = 2; max_term = 2.; max_literal = 2.; positive = 0.5 };
        };
        {
          count = 10;
          priority = Prefer_non_goals;
          weight =
            Refined { fweight = 2; vweight = 1; max_term = 2.; max_literal = 2.; positive = 2. };
        };
      ]
      @ lmax_fifo;
    ordered_rewriting = false;
    destructive_er = Er_varlit;
    avatar = false;
    unfold = None;
    prefer_initial = false;
    sine_filter = None;
    tptp_sos = false;
    loop = loop_ported;
    vampire = None;
  }

(** H----_047_B31_F1_PI_AE_R4_CS_SP_S2S: LPO4 with the invfreqconstmin precedence,
    (10.PNRefinedweight(PreferGoals,1,1,1,2,2,2,0.5),10.PNRefinedweight(PreferNonGoals,2,1,1,1,2,2,2),
    5.OrientLMaxWeight(ConstPrio,2,1,2,1,1),1.FIFOWeight(ConstPrio)), prefer_initial_clauses,
    SelectNewComplexAHP, forward_demod 1, forward contextual simplify-reflect, destructive ER on
    variable literals. Not ported: split_clauses 4 with split_aggressive. *)
let h047b31 =
  {
    name = "h047b31";
    e_name = "H----_047_B31_F1_PI_AE_R4_CS_SP_S2S";
    order = lpo4 Invfreq_constmin;
    selection = New_complex_ahp;
    queues =
      [
        {
          count = 10;
          priority = Prefer_goals;
          weight =
            Pn_refined
              {
                fweight = 1;
                vweight = 1;
                nfweight = 1;
                nvweight = 2;
                max_term = 2.;
                max_literal = 2.;
                positive = 0.5;
              };
        };
        {
          count = 10;
          priority = Prefer_non_goals;
          weight =
            Pn_refined
              {
                fweight = 2;
                vweight = 1;
                nfweight = 1;
                nvweight = 1;
                max_term = 2.;
                max_literal = 2.;
                positive = 2.;
              };
        };
      ]
      @ lmax_fifo;
    ordered_rewriting = false;
    destructive_er = Er_varlit;
    avatar = false;
    unfold = None;
    prefer_initial = true;
    sine_filter = None;
    tptp_sos = false;
    loop = loop_ported;
    vampire = None;
  }

(** Evaluation-only candidates of the member library: reachable through [--eval-strategies], not in
    [Strategy.diversified]. *)

(** G-E--_208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04AN: the [sat001] settings (KBO6, invfreq, invfreqrank,
    to_const_weight 1, the 208 mix, forward_demod 1, destructive ER, unfolding) with the non-P
    SelectComplexExceptUniqMaxHorn. (E's G-E--_208_C18_F1_SE_CS_SP_PS_S5PRR_S0Y, the second most
    used configuration of E's schedules, differs from [sat001] only in rewrite_strong_rhs_inst,
    which is inert with forward_demod 1: in this port it is [sat001].) *)
let c18 =
  {
    sat001 with
    loop = loop_ported;
    name = "c18";
    e_name = "G-E--_208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04AN";
    selection = Complex_except_uniq_max_horn;
  }

(** G-E--_208_C18_F1_SE_CS_SP_PS_S2s: the [sat001] settings with SelectCQArNT. Its SAT check is off
    in E (NoGrounding). *)
let c18s2s =
  {
    sat001 with
    name = "c18s2s";
    e_name = "G-E--_208_C18_F1_SE_CS_SP_PS_S2s";
    selection = Cq_ar_nt;
    loop = loop_ported;
  }

(** G----_X1276__C12_02_nc_F1_AE_CS_SP_S5PRR_S2S: [y1346] with the Diversityweight parameters
    (1,1,1.5,1,1,-1,0,-1,2) (E's other difference, the SAT check, is not ported), E's
    equational-definition unfolding (eqdef_incrlimit 20, as [y1346]) and E's loop details
    ({!loop_e}). *)
let x1276 =
  {
    y1346 with
    name = "x1276";
    e_name = "G----_X1276__C12_02_nc_F1_AE_CS_SP_S5PRR_S2S";
    queues =
      List.map
        (fun (q : Evaluation.queue) ->
          match q.weight with
          | Diversity d ->
              {
                q with
                weight = Diversity { d with fdiff1 = -1.; fdiff2 = 0.; vdiff1 = -1.; vdiff2 = 2. };
              }
          | _ -> q)
        y1346.queues;
    order = e_instance y1346.order;
    unfold = Some Unfold.default_limit;
    loop = loop_e;
  }

(** G----_X1276__C12_02_nc_F1_AE_CS_SP_RG_S04AN: [x1276] with SelectComplexExceptUniqMaxHorn
    (rewrite_strong_rhs_inst, also set, is inert with forward_demod 1). *)
let x1276rg =
  {
    x1276 with
    name = "x1276rg";
    e_name = "G----_X1276__C12_02_nc_F1_AE_CS_SP_RG_S04AN";
    selection = Complex_except_uniq_max_horn;
  }

(** H----_047_C09_12_F1_AE_ND_CS_SP_S2S: KBO6 with the invfreqconjmax precedence and invprecedence
    weights (to_const_weight 1), the [h047b31] queue mix
    (10.PNRefinedweight(PreferGoals,1,1,1,2,2,2,0.5),10.PNRefinedweight(PreferNonGoals,2,1,1,1,2,2,2),
    5.OrientLMaxWeight(ConstPrio,2,1,2,1,1),1.FIFOWeight(ConstPrio)) without prefer_initial,
    SelectNewComplexAHP, forward_demod 1, destructive ER on variable literals, no unfolding
    (eqdef_incrlimit is minimal in E). *)
let h047 =
  {
    h047b31 with
    name = "h047";
    e_name = "H----_047_C09_12_F1_AE_ND_CS_SP_S2S";
    order =
      {
        ordering = Kbo;
        precedence = Invfreq_conjmax;
        weights = Inv_precedence;
        const_weight = 1;
        e_signature = true;
        e_ranks = true;
      };
    prefer_initial = false;
    loop = loop_e;
  }

(** Evaluation members: E strategies that each solve problems of the development corpus that no
    default member solves, with E's loop details ({!loop_e}). *)

(** G-E--_208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN: [c18] with use_tptp_sos, so an empty set of
    support: the SimulateSOS queues prefer the initial clauses only. *)
let c18sos =
  {
    c18 with
    name = "c18sos";
    e_name = "G-E--_208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN";
    order = e_instance c18.order;
    tptp_sos = true;
    loop = loop_e;
  }

(** G-E--_208_C18C--_F1_SE_CS_SP_PS_S5PRR_RG_S04AN: [c18] with conj_only_mod 10: the symbols that
    occur only in negated-conjecture clauses rise above the rest of the invfreq precedence. *)
let c18c =
  {
    c18 with
    name = "c18c";
    e_name = "G-E--_208_C18C--_F1_SE_CS_SP_PS_S5PRR_RG_S04AN";
    order =
      {
        (e_instance c18.order) with
        precedence = Occurrence (Invfreq, { conj_only = 10; conj_axiom = 0; axiom_only = 0 });
      };
    loop = loop_e;
  }

(** G-E--_208_B07--C_F1_SE_CS_SP_PS_S5PRR_RG_S04AN: [c18] on E's LPO4 with the invfreq precedence
    and conj_axiom_mod and axiom_only_mod 10 (symbols that occur in the axioms rise above the
    conjecture-only ones). *)
let b07c =
  {
    c18 with
    name = "b07c";
    e_name = "G-E--_208_B07--C_F1_SE_CS_SP_PS_S5PRR_RG_S04AN";
    order =
      {
        (lpo4 Invfreq) with
        precedence = Occurrence (Invfreq, { conj_only = 0; conj_axiom = 10; axiom_only = 10 });
      };
    loop = loop_e;
  }

(** [c18c] behind E's SInE filter GSinE(CountFormulas,hypos,1.5,,3,20000,1.0), the filter of E's
    schedule slot that wins CSR044-10 (8,012 unit axioms): benevolence 1.5, recursion depth 3. *)
let c18csl =
  {
    c18c with
    name = "c18csl";
    e_name = "G-E--_208_C18C--_F1_SE_CS_SP_PS_S5PRR_RG_S04AN+GSinE(1.5,3)";
    sine_filter = Some (1.5, 3);
  }

(** E's SInE schedule slots for SAT001_MinMin (COM010-1) and G-E--_208_C18 (ANA012-1): the [sat001]
    and [c18] settings with E's loop details behind GSinE(1.5,3), as [c18csl]. *)
let sat001sl =
  {
    sat001 with
    name = "sat001sl";
    e_name = "SAT001_MinMin_p005000_rr_RG+GSinE(1.5,3)";
    order = e_instance sat001.order;
    sine_filter = Some (1.5, 3);
    loop = loop_e;
  }

let c18sl =
  {
    c18 with
    name = "c18sl";
    e_name = "G-E--_208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04AI+GSinE(1.5,3)";
    order = e_instance c18.order;
    sine_filter = Some (1.5, 3);
    loop = loop_e;
  }

(** G-E--_208_C18_F1_SE_CS_SP_PS_S5PRR_S4d: the [sat001] settings with SelectCQIPrecWNTNp. *)
let s4d =
  {
    sat001 with
    name = "s4d";
    e_name = "G-E--_208_C18_F1_SE_CS_SP_PS_S5PRR_S4d";
    order = e_instance sat001.order;
    selection = Cq_iprec_w_nt_np;
    loop = loop_e;
  }

(** G-E--_207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y: E's default ordering generators (to_prec_gen none =
    unary_first, to_weight_gen none = selmax, to_const_weight 0) on E's own signature, the 208 mix
    with Refinedweight(SimulateSOS,1,1,2,1.5,2), prefer_initial_clauses,
    SelectMaxLComplexAvoidPosPred, forward_demod 1, strong destructive ER. *)
let c01 =
  {
    sat001 with
    name = "c01";
    e_name = "G-E--_207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y";
    order =
      {
        ordering = Kbo;
        precedence = Unary_first;
        weights = Selmax;
        const_weight = 0;
        e_signature = true;
        e_ranks = true;
      };
    queues =
      List.map
        (fun (q : Evaluation.queue) ->
          match q.weight with
          | Refined _ ->
              {
                q with
                weight =
                  Refined
                    { fweight = 1; vweight = 1; max_term = 2.; max_literal = 1.5; positive = 2. };
              }
          | _ -> q)
        mix_208;
    prefer_initial = true;
    loop = loop_e;
  }

(** G-E--_107_C41_F1_PI_AE_CS_SP_PS_S4S: KBO6 with the invfreq precedence and precrank20 weights
    (to_const_weight 1) on E's own signature,
    (4.RelevanceLevelWeight2(SimulateSOS,0,2,1,2,100,100,100,400,1.5,1.5,1),
    3.ConjectureGeneralSymbolWeight(PreferNonGoals,200,100,200,50,50,1,100,1.5,1.5,1),
    1.Clauseweight(PreferProcessed,1,1,1),1.FIFOWeight(PreferProcessed)), prefer_initial_clauses,
    SelectNewComplexAHPNS (= SelectNewComplexAHP without split literals, which E's split_clauses 0
    never creates), forward_demod 1, destructive ER on variable literals, unfolding (eqdef_incrlimit
    20). Clauseweight is Refinedweight with both max multipliers 1 (che_clauseweight.c
    ClauseWeightCompute). *)
let c41 =
  {
    name = "c41";
    e_name = "G-E--_107_C41_F1_PI_AE_CS_SP_PS_S4S";
    order =
      {
        ordering = Kbo;
        precedence = Invfreq;
        weights = Precrank20;
        const_weight = 1;
        e_signature = true;
        e_ranks = true;
      };
    selection = New_complex_ahp;
    queues =
      [
        {
          count = 4;
          priority = Simulate_sos;
          weight =
            Relevance2
              {
                const = 0.;
                lin = 2.;
                square = 1.;
                penalty = 2;
                fweight = 100;
                cweight = 100;
                pweight = 100;
                vweight = 400;
                max_term = 1.5;
                max_literal = 1.5;
                positive = 1.;
              };
        };
        {
          count = 3;
          priority = Prefer_non_goals;
          weight =
            Conj_general
              {
                fweight = 200;
                cweight = 100;
                pweight = 200;
                conj_fweight = 50;
                conj_cweight = 50;
                conj_pweight = 1;
                vweight = 100;
                max_term = 1.5;
                max_literal = 1.5;
                positive = 1.;
              };
        };
        {
          count = 1;
          priority = Prefer_processed;
          weight =
            Refined { fweight = 1; vweight = 1; max_term = 1.; max_literal = 1.; positive = 1. };
        };
        { count = 1; priority = Prefer_processed; weight = Fifo };
      ];
    ordered_rewriting = false;
    destructive_er = Er_varlit;
    avatar = false;
    unfold = Some Unfold.default_limit;
    prefer_initial = true;
    sine_filter = None;
    tptp_sos = false;
    loop = loop_e;
    vampire = None;
  }

(** A ported heuristic with AVATAR splitting on: the same E queues, selection and ordering, plus the
    production engine's AVATAR splitting of every given clause. *)
let with_avatar h = { h with name = h.name ^ "av"; avatar = true; loop = loop_ported }

(** SInE-guided layered selection: every queue of the mix is followed by its copy restricted to the
    SInE-reachable layer ({!Sine_levels}: the axioms that SInE from the negated conjecture would
    select, and every clause with such an ancestor), with twice its count; the copy falls back to
    the whole set when that layer is empty, and the plain queues keep the turns of the clauses SInE
    would have filtered (Gleiss and Suda's two-layer selection, ratio 1:2). No axiom is filtered.
    When every axiom is reachable, or no axiom is a negated conjecture, the layer is the whole set.
*)
let with_sine_layers h =
  {
    h with
    name = h.name ^ "sl";
    e_name = h.e_name ^ "+SInE-layers";
    queues = Evaluation.layered ~cutoff:Sine_levels.reachable ~ratio:2 h.queues;
    loop = loop_ported;
  }

(** [e208] on the members' E loop with presaturation ({!loop_member}): an evaluation member
    (reachable through [--eval-strategies], not in [Strategy.diversified]). *)
let e208e = { e208 with name = "e208e"; loop = loop_member }

(** A ported Vampire slice ([Vampire.parse]) as a lean strategy. Its two queues, Vampire's age queue
    and weight queue, take [age_ratio] and [weight_ratio] selections in Vampire's balance order
    ({!Passive}); the E fields that the slice replaces keep neutral values. *)
let of_vampire name slice =
  let v = Vampire.parse slice in
  {
    name;
    e_name = "vampire:" ^ slice;
    order =
      {
        ordering = (if v.lpo then Lpo else Kbo);
        precedence = Arity;
        weights = Unit_weights;
        const_weight = 0;
        e_signature = false;
        e_ranks = false;
      };
    selection = Max_l_complex_avoid_pos_pred;
    queues =
      [
        { count = max 1 v.age_ratio; priority = Const_prio; weight = Fifo };
        { count = max 1 v.weight_ratio; priority = Const_prio; weight = Fifo };
      ];
    ordered_rewriting = false;
    destructive_er = Er_off;
    avatar = v.avatar;
    unfold = None;
    prefer_initial = false;
    sine_filter = None;
    tptp_sos = false;
    (* The ported lean loop, on which the slices were ported and measured. *)
    loop = loop_ported;
    vampire = Some v;
  }

(** Slices of Vampire 5.1.0's own schedule that solved problems of the development corpus that no
    other prover (and no member) solved, ported as evaluation baselines. The names say the selection
    and the main options, not the problems. *)
let vampire_slices =
  [
    ( "v:sos21",
      "lrs+21_1_fde=unused:sos=on:random_seed=1621186814:s2pl=no:kws=arity_squared:av=off_1" );
    ( "v:g34av",
      "lrs-34_4_fs=off:lcm=predicate:fd=off:random_seed=2917020948:aac=none:fsr=off:amm=off:er=known_2"
    );
    ( "v:lpo10av",
      "lrs+10_8:1_anc=all:to=lpo:drc=off:fs=off:bsr=unit_only:sac=on:random_seed=3389172911:fsr=off_2"
    );
    ("v:lpo1av", "lrs+1_1024_to=lpo:sp=weighted_frequency:random_seed=2199376996:amm=off_299");
    (* A slice without unit resulting resolution (Vampire with urr=off still solves the problem
       the slice was taken for), and the whole slice with it. *)
    ( "v:flr4",
      "lrs+4_2:3_slsqr=1,8:to=lpo:tgt=full:plsq=on:sp=const_min:plsqr=4,31:fd=preordered:foolp=on:gs=on:flr=on:slsq=on:random_seed=3014597381:s2pl=no:nm=0:fsd=on_3"
    );
    ("v:la1011av", "lrs+1011_1_random_seed=3389287692_2");
    (* A slice without its random age:weight choice and split queues (Vampire still solves the
       problem the slice was taken for without them). *)
    ("v:dis10", "dis+10_1024_drc=off:random_seed=1075326824:fgj=on:bd=preordered:fsr=off_7");
    ( "v:la11urr",
      "lrs+11_128_sp=unary_first:lcm=predicate:urr=on:nwc=0.5:sac=on:random_seed=1634051398:aac=none_70"
    );
    ( "v:flr4u",
      "lrs+4_2:3_slsqr=1,8:to=lpo:tgt=full:plsq=on:sp=const_min:plsqr=4,31:urr=on:fd=preordered:foolp=on:gs=on:flr=on:slsq=on:random_seed=3014597381:s2pl=no:nm=0:fsd=on_3"
    );
  ]

let named =
  [
    e208;
    e208e;
    y1346;
    sat001;
    e_kbo e208;
    e_kbo { y1346 with unfold = None };
    e_kbo sat001;
    h042;
    h047b31;
    c18;
    c18s2s;
    x1276;
    h047;
    x1276rg;
    c18sos;
    c18c;
    b07c;
    c18csl;
    sat001sl;
    c18sl;
    s4d;
    c01;
    c41;
    with_avatar e208;
    with_avatar { y1346 with unfold = None };
    with_sine_layers e208;
  ]
  @ List.map (fun (name, slice) -> of_vampire name slice) vampire_slices

let find name = List.find (fun h -> h.name = name) named
