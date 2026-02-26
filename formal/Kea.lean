-- Kea Type System Formalization
-- Lean 4 formalization of Kea's Remy-style row polymorphism and HM inference.
-- See FORMAL.md at the repo root for the Rust ↔ Lean mapping.

import Kea.Ty
import Kea.Substitution
import Kea.WellFormed
import Kea.FreeVars
import Kea.OccursCheck
import Kea.LacksConstraints
import Kea.Unify
import Kea.Generalize
import Kea.Typing
import Kea.Properties.SubstIdempotent
import Kea.Properties.SubstCompose
import Kea.Properties.SubstBridge
import Kea.Properties.WfSubstitution
import Kea.Properties.WfRename
import Kea.Properties.WfGeneralize
import Kea.Properties.UnifyReflexive
import Kea.Properties.UnifyConsistent
import Kea.Properties.UnifyExtends
import Kea.Properties.OccursCheckSound
import Kea.Properties.RowFieldsSorted
import Kea.Properties.RemyPreservesLabels
import Kea.Properties.LacksBlocksDuplicate
import Kea.Properties.DecomposeFields
