open Axiom_fuzzer
open Test_support
open Wire

(* Golden values from E 3.5.9 itself. A build of E 3.5.9's source, patched only to print each
   clause right after E evaluated it (cco_proofproc.c: ProofStateInit for initial clauses,
   insert_new_clauses for every other one) and its ordering control block, ran
   the heuristics on two corpus problems:
     E_EVAL_TRACE=1 eprover --parse-strategy=<208 body> -s GRP001-1.p   (e208)
     E_EVAL_TRACE=1 eprover --select-strategy=SAT001_MinMin_p005000_rr_RG -s GRP001-1.p
     E_EVAL_TRACE=1 eprover --parse-strategy=<208 body> -s PUZ001-1.p   (e208)
   A trace line is "EVALI|EVALD <clause> | lits=<sign><S selected><M maximal>... | sos= initial=
   processed= | [prio:weight:count]...", one bracket per queue. In an EVALI line (an input clause)
   the clause is its name in the TPTP problem instead of E's rendering of it, and the test reads it
   from the problem file; an EVALD line (a clause E derived) keeps E's. For every line the port must
   pick the same literals, mark the same literals maximal and compute the same priority and weight
   for every queue but FIFO (whose count is E's clause counter). On GRP001-1 the E-instance variants
   agree on 200 of E's 201 evaluations (e208k) and 99 of 100 (sat001k); the line left out ties two
   negative literals that E separates by its internal literal order. The first port's instance
   (e208) differs on 28 of the 201. *)

(* TPTP GRP001-1 with its include Axioms/GRP003-0.ax, and TPTP PUZ001-1, from the verbatim TPTP
   v10.0.0 files in tests/fixtures/tptp (attribution and terms: THIRD-PARTY.md). *)
let grp001 () = tptp_problem "Problems/GRP/GRP001-1.p"
let puz001 () = tptp_problem "Problems/PUZ/PUZ001-1.p"

let e208_grp001 =
  {|EVALI a_times_b_is_c | lits=+.M | sos=0 initial=1 processed=0 | [ 40:525.0000000000:11][ 40:157.5000000000:11][ 40:1.0000000000:11][ 30:525.0000000000:11][ 40:72.0000000000:11]
EVALI square_element | lits=+.M | sos=0 initial=1 processed=0 | [ 40:862.5000000000:12][ 40:1068.7500000000:12][ 40:2.0000000000:12][ 30:862.5000000000:12][ 40:60.0000000000:12]
EVALI right_identity | lits=+.M | sos=0 initial=1 processed=0 | [ 40:862.5000000000:13][ 40:1068.7500000000:13][ 40:3.0000000000:13][ 30:862.5000000000:13][ 40:60.0000000000:13]
EVALI left_identity | lits=+.M | sos=0 initial=1 processed=0 | [ 40:862.5000000000:14][ 40:1068.7500000000:14][ 40:4.0000000000:14][ 30:862.5000000000:14][ 40:60.0000000000:14]
EVALI right_inverse | lits=+.M | sos=0 initial=1 processed=0 | [ 40:1087.5000000000:15][ 40:1406.2500000000:15][ 40:5.0000000000:15][ 30:1087.5000000000:15][ 40:78.0000000000:15]
EVALI left_inverse | lits=+.M | sos=0 initial=1 processed=0 | [ 40:1087.5000000000:16][ 40:1406.2500000000:16][ 40:6.0000000000:16][ 30:1087.5000000000:16][ 40:78.0000000000:16]
EVALI prove_b_times_a_is_c | lits=-.M | sos=0 initial=1 processed=0 | [ 40:525.0000000000:17][ 40:105.0000000000:17][ 40:7.0000000000:17][ 40:525.0000000000:17][ 40:36.0000000000:17]
EVALI total_function1 | lits=+.M | sos=0 initial=1 processed=0 | [ 40:1312.5000000000:18][ 40:1743.7500000000:18][ 40:8.0000000000:18][ 30:1312.5000000000:18][ 40:84.0000000000:18]
EVALI total_function2 | lits=+.M-.M-.M | sos=0 initial=1 processed=0 | [ 40:2175.0000000000:19][ 40:2100.0000000000:19][ 40:9.0000000000:19][ 30:2175.0000000000:19][ 40:87.0000000000:19]
EVALI associativity2 | lits=+.M-.M-.M-.M | sos=0 initial=1 processed=0 | [ 40:3450.0000000000:20][ 40:3206.2500000000:20][ 40:10.0000000000:20][ 30:3450.0000000000:20][ 40:135.0000000000:20]
EVALI associativity1 | lits=+.M-.M-.M-.M | sos=0 initial=1 processed=0 | [ 40:3450.0000000000:21][ 40:3206.2500000000:21][ 40:11.0000000000:21][ 30:3450.0000000000:21][ 40:135.0000000000:21]
EVALD cnf(i_0_23, negated_conjecture, (X1=c|~product(a,b,X1))). | lits=+..-.M | sos=0 initial=0 processed=0 | [ 50:862.5000000000:33][ 40:555.0000000000:33][ 40:23.0000000000:33][ 30:862.5000000000:33][ 50:59.0000000000:33]
EVALD cnf(i_0_24, plain, (X1=identity|~product(inverse(X2),X2,X1))). | lits=+..-.M | sos=0 initial=0 processed=0 | [ 50:1387.5000000000:34][ 40:1387.5000000000:34][ 40:24.0000000000:34][ 30:1387.5000000000:34][ 50:62.0000000000:34]
EVALD cnf(i_0_25, plain, (X1=X2|~product(identity,X2,X1))). | lits=+..-.M | sos=0 initial=0 processed=0 | [ 50:1162.5000000000:35][ 40:1162.5000000000:35][ 40:25.0000000000:35][ 30:1162.5000000000:35][ 50:52.0000000000:35]
EVALD cnf(i_0_26, plain, (X1=identity|~product(X2,inverse(X2),X1))). | lits=+..-.M | sos=0 initial=0 processed=0 | [ 50:1387.5000000000:36][ 40:1387.5000000000:36][ 40:26.0000000000:36][ 30:1387.5000000000:36][ 50:62.0000000000:36]
EVALD cnf(i_0_27, plain, (X1=X2|~product(X2,identity,X1))). | lits=+..-.M | sos=0 initial=0 processed=0 | [ 50:1162.5000000000:37][ 40:1162.5000000000:37][ 40:27.0000000000:37][ 30:1162.5000000000:37][ 50:52.0000000000:37]
EVALD cnf(i_0_28, plain, (X1=multiply(X2,X3)|~product(X2,X3,X1))). | lits=+SM-SM | sos=0 initial=0 processed=0 | [ 50:1762.5000000000:38][ 40:2062.5000000000:38][ 40:28.0000000000:38][ 30:1762.5000000000:38][ 50:90.0000000000:38]
EVALD cnf(i_0_29, plain, (X1=identity|~product(X2,X2,X1))). | lits=+..-.M | sos=0 initial=0 processed=0 | [ 50:1162.5000000000:39][ 40:1162.5000000000:39][ 40:29.0000000000:39][ 30:1162.5000000000:39][ 50:53.0000000000:39]
EVALD cnf(i_0_30, negated_conjecture, (product(X1,b,X2)|~product(X3,c,X2)|~product(X3,a,X1))). | lits=+SM-SM-.. | sos=0 initial=0 processed=0 | [ 50:2000.0000000000:40][ 40:1615.0000000000:40][ 40:30.0000000000:40][ 30:2000.0000000000:40][ 50:110.0000000000:40]
EVALD cnf(i_0_31, plain, (product(X1,X2,X3)|~product(X4,identity,X3)|~product(X4,inverse(X2),X1))). | lits=+SM-..-SM | sos=0 initial=0 processed=0 | [ 50:2525.0000000000:41][ 40:2481.2500000000:41][ 40:31.0000000000:41][ 30:2525.0000000000:41][ 50:110.0000000000:41]
EVALD cnf(i_0_32, plain, (product(X1,X2,X3)|~product(X4,X2,X3)|~product(X4,identity,X1))). | lits=+SM-..-SM | sos=0 initial=0 processed=0 | [ 50:2300.0000000000:42][ 40:2256.2500000000:42][ 40:32.0000000000:42][ 30:2300.0000000000:42][ 50:102.0000000000:42]
EVALD cnf(i_0_33, plain, (product(X1,inverse(X2),X3)|~product(X4,identity,X3)|~product(X4,X2,X1))). | lits=+SM-SM-.. | sos=0 initial=0 processed=0 | [ 50:2525.0000000000:43][ 40:2593.7500000000:43][ 40:33.0000000000:43][ 30:2525.0000000000:43][ 50:120.0000000000:43]
EVALD cnf(i_0_34, plain, (product(X1,identity,X2)|~product(X4,X3,X2)|~product(X4,X3,X1))). | lits=+SM-SM-.. | sos=0 initial=0 processed=0 | [ 50:2300.0000000000:44][ 40:2256.2500000000:44][ 40:34.0000000000:44][ 30:2300.0000000000:44][ 50:105.0000000000:44]
EVALD cnf(i_0_35, plain, (product(X1,X2,X3)|~product(X5,multiply(X4,X2),X3)|~product(X5,X4,X1))). | lits=+SM-SM-.. | sos=0 initial=0 processed=0 | [ 50:2750.0000000000:45][ 40:2706.2500000000:45][ 40:35.0000000000:45][ 30:2750.0000000000:45][ 50:114.0000000000:45]
EVALD cnf(i_0_36, plain, (product(X1,X2,X3)|~product(X4,identity,X3)|~product(X4,X2,X1))). | lits=+SM-SM-.. | sos=0 initial=0 processed=0 | [ 50:2300.0000000000:46][ 40:2256.2500000000:46][ 40:36.0000000000:46][ 30:2300.0000000000:46][ 50:102.0000000000:46]
EVALD cnf(i_0_37, negated_conjecture, (product(X1,X2,c)|~product(X3,b,X2)|~product(X1,X3,a))). | lits=+SM-SM-.. | sos=0 initial=0 processed=0 | [ 50:2000.0000000000:47][ 40:1615.0000000000:47][ 40:37.0000000000:47][ 30:2000.0000000000:47][ 50:110.0000000000:47]
EVALD cnf(i_0_38, plain, (product(X1,X2,identity)|~product(X4,X3,X2)|~product(X1,X4,inverse(X3)))). | lits=+SM-..-SM | sos=0 initial=0 processed=0 | [ 50:2525.0000000000:48][ 40:2481.2500000000:48][ 40:38.0000000000:48][ 30:2525.0000000000:48][ 50:114.0000000000:48]
EVALD cnf(i_0_39, plain, (product(X1,X2,X3)|~product(X4,X3,X2)|~product(X1,X4,identity))). | lits=+SM-..-SM | sos=0 initial=0 processed=0 | [ 50:2300.0000000000:49][ 40:2256.2500000000:49][ 40:39.0000000000:49][ 30:2300.0000000000:49][ 50:102.0000000000:49]
EVALD cnf(i_0_40, plain, (product(X1,X2,identity)|~product(X4,inverse(X3),X2)|~product(X1,X4,X3))). | lits=+SM-SM-.. | sos=0 initial=0 processed=0 | [ 50:2525.0000000000:50][ 40:2481.2500000000:50][ 40:40.0000000000:50][ 30:2525.0000000000:50][ 50:114.0000000000:50]
EVALD cnf(i_0_41, plain, (product(X1,X2,X3)|~product(X4,identity,X2)|~product(X1,X4,X3))). | lits=+SM-SM-.. | sos=0 initial=0 processed=0 | [ 50:2300.0000000000:51][ 40:2256.2500000000:51][ 40:41.0000000000:51][ 30:2300.0000000000:51][ 50:102.0000000000:51]
EVALD cnf(i_0_42, plain, (product(X1,X2,multiply(X3,X4))|~product(X5,X4,X2)|~product(X1,X5,X3))). | lits=+SM-SM-.. | sos=0 initial=0 processed=0 | [ 50:2750.0000000000:52][ 40:2931.2500000000:52][ 40:42.0000000000:52][ 30:2750.0000000000:52][ 50:129.0000000000:52]
EVALD cnf(i_0_44, negated_conjecture, (multiply(a,b)=c)). | lits=+.M | sos=0 initial=0 processed=0 | [ 50:525.0000000000:54][ 40:427.5000000000:54][ 40:44.0000000000:54][ 30:525.0000000000:54][ 50:72.0000000000:54]
EVALD cnf(i_0_46, plain, (inverse(identity)=identity)). | lits=+.M | sos=0 initial=0 processed=0 | [ 50:600.0000000000:55][ 40:900.0000000000:55][ 40:45.0000000000:55][ 30:600.0000000000:55][ 50:54.0000000000:55]|}

let sat001_grp001 =
  {|EVALI a_times_b_is_c | lits=+.M | sos=0 initial=1 processed=0 | [ 40:525.0000000000:11][ 40:157.5000000000:11][ 40:1.0000000000:11][ 30:525.0000000000:11][ 40:72.0000000000:11]
EVALI square_element | lits=+.M | sos=0 initial=1 processed=0 | [ 40:862.5000000000:12][ 40:1068.7500000000:12][ 40:2.0000000000:12][ 30:862.5000000000:12][ 40:60.0000000000:12]
EVALI right_identity | lits=+.M | sos=0 initial=1 processed=0 | [ 40:862.5000000000:13][ 40:1068.7500000000:13][ 40:3.0000000000:13][ 30:862.5000000000:13][ 40:60.0000000000:13]
EVALD cnf(i_0_23, negated_conjecture, (X1=c|~product(a,b,X1))). | lits=+..-.M | sos=0 initial=0 processed=0 | [ 50:862.5000000000:33][ 40:555.0000000000:33][ 40:23.0000000000:33][ 30:862.5000000000:33][ 50:59.0000000000:33]
EVALD cnf(i_0_24, plain, (X1=identity|~product(inverse(X2),X2,X1))). | lits=+..-.M | sos=0 initial=0 processed=0 | [ 50:1387.5000000000:34][ 40:1387.5000000000:34][ 40:24.0000000000:34][ 30:1387.5000000000:34][ 50:62.0000000000:34]
EVALD cnf(i_0_25, plain, (X1=X2|~product(identity,X2,X1))). | lits=+..-.M | sos=0 initial=0 processed=0 | [ 50:1162.5000000000:35][ 40:1162.5000000000:35][ 40:25.0000000000:35][ 30:1162.5000000000:35][ 50:52.0000000000:35]
EVALD cnf(i_0_26, plain, (X1=identity|~product(X2,inverse(X2),X1))). | lits=+..-.M | sos=0 initial=0 processed=0 | [ 50:1387.5000000000:36][ 40:1387.5000000000:36][ 40:26.0000000000:36][ 30:1387.5000000000:36][ 50:62.0000000000:36]
EVALD cnf(i_0_28, plain, (X1=multiply(X2,X3)|~product(X2,X3,X1))). | lits=+..-SM | sos=0 initial=0 processed=0 | [ 50:1462.5000000000:38][ 40:1612.5000000000:38][ 40:28.0000000000:38][ 30:1462.5000000000:38][ 50:69.0000000000:38]
EVALD cnf(i_0_30, negated_conjecture, (product(X1,b,X2)|~product(X3,c,X2)|~product(X3,a,X1))). | lits=+..-SM-.. | sos=0 initial=0 processed=0 | [ 50:1750.0000000000:40][ 40:1360.0000000000:40][ 40:30.0000000000:40][ 30:1750.0000000000:40][ 50:90.0000000000:40]
EVALD cnf(i_0_31, plain, (product(X1,X2,X3)|~product(X4,identity,X3)|~product(X4,inverse(X2),X1))). | lits=+..-..-SM | sos=0 initial=0 processed=0 | [ 50:2237.5000000000:41][ 40:2125.0000000000:41][ 40:31.0000000000:41][ 30:2237.5000000000:41][ 50:92.0000000000:41]
EVALD cnf(i_0_32, plain, (product(X1,X2,X3)|~product(X4,X2,X3)|~product(X4,identity,X1))). | lits=+..-..-SM | sos=0 initial=0 processed=0 | [ 50:2012.5000000000:42][ 40:1900.0000000000:42][ 40:32.0000000000:42][ 30:2012.5000000000:42][ 50:84.0000000000:42]
EVALD cnf(i_0_33, plain, (product(X1,inverse(X2),X3)|~product(X4,identity,X3)|~product(X4,X2,X1))). | lits=+..-SM-.. | sos=0 initial=0 processed=0 | [ 50:2162.5000000000:43][ 40:2125.0000000000:43][ 40:33.0000000000:43][ 30:2162.5000000000:43][ 50:96.0000000000:43]|}

let e208_puz001 =
  {|EVALI agatha | lits=+.M | sos=0 initial=1 processed=0 | [ 40:412.5000000000:12][ 40:393.7500000000:12][ 40:1.0000000000:12][ 30:412.5000000000:12][ 40:36.0000000000:12]
EVALI butler | lits=+.M | sos=0 initial=1 processed=0 | [ 40:412.5000000000:13][ 40:393.7500000000:13][ 40:2.0000000000:13][ 30:412.5000000000:13][ 40:36.0000000000:13]
EVALI charles | lits=+.M | sos=0 initial=1 processed=0 | [ 40:412.5000000000:14][ 40:393.7500000000:14][ 40:3.0000000000:14][ 30:412.5000000000:14][ 40:36.0000000000:14]
EVALI agatha_hates_agatha | lits=+.M | sos=0 initial=1 processed=0 | [ 40:525.0000000000:15][ 40:427.5000000000:15][ 40:4.0000000000:15][ 30:525.0000000000:15][ 40:54.0000000000:15]
EVALI agatha_hates_charles | lits=+.M | sos=0 initial=1 processed=0 | [ 40:525.0000000000:16][ 40:427.5000000000:16][ 40:5.0000000000:16][ 30:525.0000000000:16][ 40:54.0000000000:16]
EVALI prove_neither_charles_nor_butler_did_it | lits=+..+.M | sos=0 initial=1 processed=0 | [ 40:687.5000000000:17][ 40:206.2500000000:17][ 40:6.0000000000:17][ 30:687.5000000000:17][ 40:90.0000000000:17]
EVALI butler_hates_poor | lits=+..+..-.M | sos=0 initial=1 processed=0 | [ 40:1375.0000000000:18][ 40:1440.0000000000:18][ 40:7.0000000000:18][ 30:1375.0000000000:18][ 40:79.0000000000:18]
EVALI same_hates | lits=+.M-.. | sos=0 initial=1 processed=0 | [ 40:1062.5000000000:19][ 40:1056.2500000000:19][ 40:8.0000000000:19][ 30:1062.5000000000:19][ 40:64.0000000000:19]
EVALI killer_hates_victim | lits=+..-.M | sos=0 initial=1 processed=0 | [ 40:1137.5000000000:20][ 40:1177.5000000000:20][ 40:9.0000000000:20][ 30:1137.5000000000:20][ 40:49.0000000000:20]
EVALI different_hates | lits=-..-.M | sos=0 initial=1 processed=0 | [ 40:1062.5000000000:21][ 40:812.5000000000:21][ 40:10.0000000000:21][ 40:1062.5000000000:21][ 40:40.0000000000:21]
EVALI poorer_killer | lits=-..-.M | sos=0 initial=1 processed=0 | [ 40:1175.0000000000:22][ 40:1015.0000000000:22][ 40:11.0000000000:22][ 40:1175.0000000000:22][ 40:35.0000000000:22]
EVALI no_one_hates_everyone | lits=-..-..-.M | sos=0 initial=1 processed=0 | [ 40:1487.5000000000:23][ 40:1137.5000000000:23][ 40:12.0000000000:23][ 40:1487.5000000000:23][ 40:56.0000000000:23]
EVALD cnf(i_0_25, negated_conjecture, (hates(charles,agatha)|killed(butler,agatha))). | lits=+..+.M | sos=0 initial=0 processed=0 | [ 50:762.5000000000:36][ 40:408.7500000000:36][ 40:25.0000000000:36][ 30:762.5000000000:36][ 50:90.0000000000:36]
EVALD cnf(i_0_26, hypothesis, (~hates(agatha,butler))). | lits=-.M | sos=1 initial=0 processed=0 | [ 40:525.0000000000:37][ 40:285.0000000000:37][ 40:26.0000000000:37][ 40:525.0000000000:37][ 40:27.0000000000:37]
EVALD cnf(i_0_27, negated_conjecture, (hates(butler,agatha)|hates(charles,agatha))). | lits=+..+.M | sos=0 initial=0 processed=0 | [ 50:875.0000000000:38][ 40:712.5000000000:38][ 40:27.0000000000:38][ 30:875.0000000000:38][ 50:90.0000000000:38]
EVALD cnf(i_0_28, negated_conjecture, (hates(butler,agatha))). | lits=+.M | sos=1 initial=0 processed=0 | [ 40:525.0000000000:39][ 40:427.5000000000:39][ 40:28.0000000000:39][ 30:525.0000000000:39][ 40:54.0000000000:39]
EVALD cnf(i_0_29, hypothesis, (~hates(butler,butler))). | lits=-.M | sos=1 initial=0 processed=0 | [ 40:525.0000000000:40][ 40:285.0000000000:40][ 40:29.0000000000:40][ 40:525.0000000000:40][ 40:27.0000000000:40]
EVALD cnf(i_0_30, hypothesis, (hates(butler,charles)|richer(charles,agatha))). | lits=+..+.M | sos=0 initial=0 processed=0 | [ 50:875.0000000000:41][ 40:712.5000000000:41][ 40:30.0000000000:41][ 30:875.0000000000:41][ 50:90.0000000000:41]
EVALD cnf(i_0_31, hypothesis, (hates(butler,butler)|richer(butler,agatha))). | lits=+..+.M | sos=0 initial=0 processed=0 | [ 50:875.0000000000:42][ 40:712.5000000000:42][ 40:31.0000000000:42][ 30:875.0000000000:42][ 50:90.0000000000:42]
EVALD cnf(i_0_33, hypothesis, (hates(butler,charles)|~killed(charles,agatha))). | lits=+..-.M | sos=1 initial=0 processed=0 | [ 40:762.5000000000:43][ 40:367.5000000000:43][ 40:32.0000000000:43][ 30:762.5000000000:43][ 40:63.0000000000:43]
EVALD cnf(i_0_34, hypothesis, (~hates(agatha,butler))). | lits=-.M | sos=1 initial=0 processed=0 | [ 40:525.0000000000:44][ 40:285.0000000000:44][ 40:33.0000000000:44][ 40:525.0000000000:44][ 40:27.0000000000:44]
EVALD cnf(i_0_35, negated_conjecture, (hates(butler,charles)|killed(butler,agatha))). | lits=+.M+.. | sos=1 initial=0 processed=0 | [ 40:800.0000000000:45][ 40:510.0000000000:45][ 40:34.0000000000:45][ 30:800.0000000000:45][ 40:90.0000000000:45]
EVALD cnf(i_0_36, negated_conjecture, (killed(butler,agatha)|~hates(butler,butler))). | lits=+.M-.. | sos=1 initial=0 processed=0 | [ 40:762.5000000000:46][ 40:313.7500000000:46][ 40:35.0000000000:46][ 30:762.5000000000:46][ 40:72.0000000000:46]
EVALD cnf(i_0_37, hypothesis, (~killed(butler,agatha))). | lits=-.M | sos=1 initial=0 processed=0 | [ 40:412.5000000000:47][ 40:82.5000000000:47][ 40:36.0000000000:47][ 40:412.5000000000:47][ 40:27.0000000000:47]
EVALD cnf(i_0_24, negated_conjecture, (killed(charles,agatha))). | lits=+.M | sos=1 initial=0 processed=1 | [ 40:412.5000000000:48][ 40:123.7500000000:48][ 30:37.0000000000:48][ 30:412.5000000000:48][ 40:54.0000000000:48]
EVALD cnf(i_0_25, negated_conjecture, (hates(charles,agatha))). | lits=+.M | sos=1 initial=0 processed=1 | [ 40:525.0000000000:49][ 40:427.5000000000:49][ 30:38.0000000000:49][ 30:525.0000000000:49][ 40:54.0000000000:49]
EVALD cnf(i_0_35, negated_conjecture, (hates(butler,charles))). | lits=+.M | sos=1 initial=0 processed=1 | [ 40:525.0000000000:50][ 40:427.5000000000:50][ 30:39.0000000000:50][ 30:525.0000000000:50][ 40:54.0000000000:50]
EVALD cnf(i_0_33, hypothesis, (hates(butler,charles))). | lits=+.M | sos=1 initial=0 processed=1 | [ 40:525.0000000000:51][ 40:427.5000000000:51][ 30:40.0000000000:51][ 30:525.0000000000:51][ 40:54.0000000000:51]
EVALD cnf(i_0_38, negated_conjecture, (hates(charles,agatha))). | lits=+.M | sos=1 initial=0 processed=0 | [ 40:525.0000000000:52][ 40:427.5000000000:52][ 40:41.0000000000:52][ 30:525.0000000000:52][ 40:54.0000000000:52]|}

let index_of s sub from =
  let n = String.length sub in
  let rec go i =
    if i + n > String.length s then raise Not_found
    else if String.sub s i n = sub then i
    else go (i + 1)
  in
  go from

let between s a b =
  let i = index_of s a 0 + String.length a in
  String.sub s i (index_of s b i - i)

let after s a =
  let i = index_of s a 0 + String.length a in
  String.sub s i (String.length s - i)

let contains s sub = match index_of s sub 0 with _ -> true | exception Not_found -> false

let check_trace ~name ~problem ~heuristic ~goals trace =
  let h = List.find (fun (h : Heuristic.t) -> h.name = heuristic) Heuristic.named in
  let theory = Tptp.parse problem in
  let clauses a = Clausify.run ~mode:Hybrid a in
  let table, violations = Eorder.table h.order (List.concat_map clauses (Theory.fixed theory)) in
  equal violations [] (name ^ ": admissibility repairs");
  let order = Ordering.create () in
  Ordering.install_table ~unified:h.order.e_signature order table;
  let conjecture =
    Some
      (Evaluation.conjecture_symbols
         (List.concat_map clauses
            (List.filter (fun (a : axiom) -> List.mem a.name goals) (Theory.fixed theory))))
  in
  let checked = ref 0 in
  List.iter
    (fun line ->
      if String.length line > 6 then (
        incr checked;
        let context = Printf.sprintf "%s line %d" name !checked in
        let clause =
          if String.starts_with ~prefix:"EVALI " line then
            (* An input clause, named as in the problem. *)
            let name = String.trim (between line "EVALI " " | lits=") in
            match List.filter (fun (a : axiom) -> a.name = name) (Theory.fixed theory) with
            | [ a ] -> Clause.normalize (List.hd (clauses a))
            | _ -> failwith (context ^ ": no input clause " ^ name)
          else
            let body = between line ", " ")). |" in
            let body =
              String.sub body
                (String.index body ',' + 1)
                (String.length body - String.index body ',' - 1)
            in
            match Theory.fixed (Tptp.parse ("cnf(c,axiom," ^ String.trim body ^ ")).")) with
            | [ a ] -> Clause.normalize (List.hd (clauses a))
            | _ -> failwith (context ^ ": parse")
        in
        let props = "sos=" ^ between line "| sos=" " | [" in
        let get key =
          let n = String.length key in
          let rec go i = if String.sub props i n = key then props.[i + n] = '1' else go (i + 1) in
          go 0
        in
        let facts =
          {
            Evaluation.initial = get "initial=";
            sos = get "sos=";
            processed = get "processed=";
            conjecture;
            age = 0;
            level = 0;
            relevance = None;
          }
        in
        (* Selected and maximal literals, as a multiset of sign/selected/maximal codes. *)
        let code = between line "| lits=" " |" in
        let expected_codes =
          List.init
            (String.length code / 3)
            (fun i ->
              let c = String.sub code (3 * i) 3 in
              (* E selects literals of initial clauses only when they are processed. *)
              if facts.initial then String.mapi (fun j ch -> if j = 1 then '.' else ch) c else c)
          |> List.sort compare
        in
        let selection =
          if facts.initial then None else Eselection.select ~order h.selection clause
        in
        let flags = Eselection.selected_maximal_flags ~order clause selection in
        let codes =
          List.mapi
            (fun i l ->
              let selected = match selection with Some js -> List.mem i js | None -> false in
              Printf.sprintf "%c%c%c"
                (if l.positive then '+' else '-')
                (if selected then 'S' else '.')
                (if flags.(i) then 'M' else '.'))
            clause
          |> List.sort compare
        in
        equal codes expected_codes (context ^ ": selected and maximal literals");
        let evals = Evaluation.evaluate ~order ~selection:h.selection h.queues facts clause in
        let expected =
          String.split_on_char '[' (after line " | [")
          |> List.filter_map (fun cell ->
              match String.split_on_char ':' (String.trim cell) with
              | [ p; w; _ ] -> Some (int_of_string (String.trim p), float_of_string w)
              | _ -> None)
        in
        List.iteri
          (fun i (q : Evaluation.queue) ->
            match q.weight with
            | Fifo -> ()
            | _ ->
                let p, w = evals.(i) and ep, ew = List.nth expected i in
                equal p ep (Printf.sprintf "%s: queue %d priority" context i);
                check
                  (Float.abs (w -. ew) <= 1e-6 *. Float.max 1. ew)
                  (Printf.sprintf "%s: queue %d weight %.4f, E %.4f" context i w ew))
          h.queues))
    (String.split_on_char '\n' trace);
  !checked

let tests =
  [
    ( "E's own KBO instance: GRP001-1 weights as E 3.5.9 prints them for the 208 heuristic",
      fun () ->
        let theory = Tptp.parse (grp001 ()) in
        let clauses = List.concat_map (Clausify.run ~mode:Hybrid) (Theory.fixed theory) in
        let weight h key =
          let table, _ = Eorder.table (Heuristic.find h).order clauses in
          snd (Hashtbl.find table key)
        in
        let f name arity = (Ordering.Function (Original name), arity) in
        (* E: identity 1, a 2, b 3, c 4, $false 5, product 6, multiply 7, ..., inverse 28 (the
           twenty internal non-constant symbols lie between multiply and the top unary symbol). *)
        List.iter
          (fun (key, w) -> equal (weight "e208k" key) w "e208k weight")
          [
            (f "identity" 0, 1);
            (f "a" 0, 2);
            (f "b" 0, 3);
            (f "c" 0, 4);
            ((Ordering.Predicate "product", 3), 6);
            (f "multiply" 2, 7);
            (f "inverse" 1, 28);
          ];
        (* The first port's instance makes every constant weigh 1 and leaves the internal
           symbols out. *)
        equal (weight "e208" (f "b" 0)) 1 "e208 constant weight";
        equal (weight "e208" (f "inverse" 1)) 7 "e208 top weight" );
    ( "e208k reproduces E's selection, maximality and evaluations on GRP001-1",
      fun () ->
        let n =
          check_trace ~name:"e208k GRP001-1" ~problem:(grp001 ()) ~heuristic:"e208k"
            ~goals:[ "a_times_b_is_c"; "prove_b_times_a_is_c" ]
            e208_grp001
        in
        equal n 33 "trace lines" );
    ( "sat001k reproduces E's selection, maximality and evaluations on GRP001-1",
      fun () ->
        let n =
          check_trace ~name:"sat001k GRP001-1" ~problem:(grp001 ()) ~heuristic:"sat001k"
            ~goals:[ "a_times_b_is_c"; "prove_b_times_a_is_c" ]
            sat001_grp001
        in
        equal n 12 "trace lines" );
    ( "e208k reproduces E's set-of-support priorities and evaluations on PUZ001-1",
      fun () ->
        let n =
          check_trace ~name:"e208k PUZ001-1" ~problem:(puz001 ()) ~heuristic:"e208k"
            ~goals:[ "prove_neither_charles_nor_butler_did_it" ]
            e208_puz001
        in
        equal n 29 "trace lines";
        check
          (List.exists
             (fun l -> contains l "EVALD" && contains l "sos=1")
             (String.split_on_char '\n' e208_puz001))
          "the trace has no set-of-support clause" );
  ]

let () = run tests
