# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* The energy identity is stated as a sum over ordered adjacent pairs, with a separate theorem
  that the two orientations of each edge are equal. The sum is not rewritten over the graph's
  unordered edge set.
* The holonomy description (3) is proved in one direction: a parallel section is fixed by the
  holonomy of every loop, i.e. commutes with it. The converse is not formalized: on a connected
  graph, a base block fixed by all holonomies extends to a parallel section. That direction is
  the classical correspondence the note cites.
* The Frobenius energy of the block matrix is defined blockwise, as the sum of the Frobenius
  energies of its blocks.
