-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet
/-!
# Axiom audit — every headline item, transitively axiom-free

`scripts/check-proofs.sh lean4` runs this file and requires one
"does not depend on any axioms" line per `#print axioms` command below
(and no `sorryAx` anywhere in the output). A theorem that elaborates but
smuggles in an axiom or a `sorry` through an import fails the gate here,
not in a status document. Update the PROOF-STATUS ledger when adding lines.
-/

-- MECH-1 (L1): totality core + stability
#print axioms Systemet.L1.substTy
#print axioms Systemet.L1.substNf
#print axioms Systemet.L1.appSp
#print axioms Systemet.L1.nf
#print axioms Systemet.L1.spKindLe
#print axioms Systemet.L1.nf_emb
#print axioms Systemet.L1.nf_embSp

-- MECH-2 (L2): the grade-algebra law set and its instances
#print axioms Systemet.L2.Affine.grade
#print axioms Systemet.L2.Cost.grade
#print axioms Systemet.L2.BoundedDistLattice.grade
#print axioms Systemet.L2.Level.lattice
#print axioms Systemet.L2.prodGrade

-- MECH-1 (L1) milestone 2: ET-2 — conversion is decidable
#print axioms Systemet.L1.nf_substTy
#print axioms Systemet.L1.substNf_substNf
#print axioms Systemet.L1.defEq_substTy_embNf
#print axioms Systemet.L1.soundness
#print axioms Systemet.L1.completeness
#print axioms Systemet.L1.defEq_iff_nf
#print axioms Systemet.L1.decEqNf
#print axioms Systemet.L1.decDefEq
