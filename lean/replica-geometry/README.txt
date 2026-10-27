LEAN 4 CERTIFICATE: REPLICA GEOMETRY

Companion to "Large deviations for the maximum of the generalized TAP free
energy", by Jeanne Boursier.

BarycenterGeometry.lean contains eleven checked theorems about finite
replica geometry, partition-weight normalization, and a conditional
algebraic obstruction to a barycenter-only rate formula.

The main geometric theorem works in any real inner-product space. For
k positive, N>0, q=||m||^2/N, delta>=0, and vectors sigma_i satisfying

  ||sigma_i||^2=N,
  |<sigma_i,m>/N-q|<=delta,
  |<sigma_i,sigma_j>/N-q|<=delta for i != j,

it proves

  ||k^(-1) sum_i sigma_i-m||^2/N <= (1-q)/k+3 delta.

The file also proves the exact normalization identities for positive
partition weights. The final rate-gap statements are conditional on
explicit thermodynamic inequalities; those inequalities are hypotheses
of the Lean theorems.

The Gaussian estimates, Parisi formula, generalized TAP approximation,
and thermodynamic/large-deviation limits are outside this formalization.

BUILD

Install Lean through elan, then run:

  git clone https://github.com/jboursier/jboursier.github.io.git
  cd jboursier.github.io/lean/replica-geometry
  lake exe cache get
  lake build

The project pins Lean 4.35.0 and mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679. Transitive dependency revisions
are recorded in lake-manifest.json.

The source ends with #print axioms checks for all eleven named theorems.
Their dependencies are propext, Classical.choice, and Quot.sound. There
are no admitted proofs or additional axioms in this certificate.

Source SHA256:
e98da9fd999f7f054d91fa0844b7a3cb0a9d32752f400f9cb2adf930883ab901
