initSidebarItems({"constant":[["MAX_ACCUMULATOR_LEAVES",""],["MAX_ACCUMULATOR_PROOF_DEPTH",""]],"struct":[["AccountStateProof","The complete proof used to authenticate the state of an account. This structure consists of the `AccumulatorProof` from `LedgerInfo` to `TransactionInfo`, the `TransactionInfo` object and the `SparseMerkleProof` from state root to the account."],["AccumulatorConsistencyProof","A proof that can be used to show that two Merkle accumulators are consistent – the big one can be obtained by appending certain leaves to the small one. For example, at some point in time a client knows that the root hash of the ledger at version 10 is `old_root` (it could be a waypoint). If a server wants to prove that the new ledger at version `N` is derived from the old ledger the client knows, it can show the subtrees that represent all the new leaves. If the client can verify that it can indeed obtain the new root hash by appending these new leaves, it can be convinced that the two accumulators are consistent."],["AccumulatorExtensionProof","A proof that first verifies that establishes correct computation of the root and then returns the new tree to acquire a new root and version."],["AccumulatorProof","A proof that can be used authenticate an element in an accumulator given trusted root hash. For example, both `LedgerInfoToTransactionInfoProof` and `TransactionInfoToEventProof` can be constructed on top of this structure."],["AccumulatorRangeProof","A proof that is similar to `AccumulatorProof`, but can be used to authenticate a range of leaves. For example, given the following accumulator:"],["EventProof","The complete proof used to authenticate a contract event. This structure consists of the `AccumulatorProof` from `LedgerInfo` to `TransactionInfo`, the `TransactionInfo` object and the `AccumulatorProof` from event accumulator root to the event."],["SparseMerkleProof","A proof that can be used to authenticate an element in a Sparse Merkle Tree given trusted root hash. For example, `TransactionInfoToAccountProof` can be constructed on top of this structure."],["SparseMerkleRangeProof","A proof that can be used authenticate a range of consecutive leaves, from the leftmost leaf to a certain one, in a sparse Merkle tree. For example, given the following sparse Merkle tree:"],["TransactionAccumulatorSummary","An in-memory accumulator for storing a summary of the core transaction info accumulator. It is a summary in the sense that it only stores maximally frozen subtree nodes rather than storing all leaves and internal nodes."],["TransactionInfoWithProof","`TransactionInfo` and a `TransactionAccumulatorProof` connecting it to the ledger root."],["TransactionListProof","The complete proof used to authenticate a list of consecutive transactions."]],"type":[["EventAccumulatorProof",""],["LeafCount","Because leaves can only take half the space in the tree, any numbering of the tree leaves must not take the full width of the total space.  Thus, for a 64-bit ordering, our maximumm proof depth is limited to 63."],["TestAccumulatorProof",""],["TestAccumulatorRangeProof",""],["TransactionAccumulatorProof",""],["TransactionAccumulatorRangeProof",""]]});