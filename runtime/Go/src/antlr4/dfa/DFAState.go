package antlr

var ATNConfigSet = require('./../atn/ATNConfigSet').ATNConfigSet;

// Map a predicate to a predicted alternative.///

function PredPrediction(pred, alt) {
	this.alt = alt;
	this.pred = pred;
	return this;
}

func (this *PredPrediction) toString() {
	return "(" + this.pred + ", " + this.alt + ")";
}

// A DFA state represents a set of possible ATN configurations.
// As Aho, Sethi, Ullman p. 117 says "The DFA uses its state
// to keep track of all possible states the ATN can be in after
// reading each input symbol. That is to say, after reading
// input a1a2..an, the DFA is in a state that represents the
// subset T of the states of the ATN that are reachable from the
// ATN's start state along some path labeled a1a2..an."
// In conventional NFA&rarr;DFA conversion, therefore, the subset T
// would be a bitset representing the set of states the
// ATN could be in. We need to track the alt predicted by each
// state as well, however. More importantly, we need to maintain
// a stack of states, tracking the closure operations as they
// jump from rule to rule, emulating rule invocations (method calls).
// I have to add a stack to simulate the proper lookahead sequences for
// the underlying LL grammar from which the ATN was derived.
//
// <p>I use a set of ATNConfig objects not simple states. An ATNConfig
// is both a state (ala normal conversion) and a RuleContext describing
// the chain of rules (if any) followed to arrive at that state.</p>
//
// <p>A DFA state may have multiple references to a particular state,
// but with different ATN contexts (with same or different alts)
// meaning that state was reached via a different set of rule invocations.</p>
// /

function DFAState(stateNumber, configs) {
	if (stateNumber == null) {
		stateNumber = -1;
	}
	if (configs == null) {
		configs = new ATNConfigSet();
	}
	this.stateNumber = stateNumber;
	this.configs = configs;
	// {@code edges[symbol]} points to target of symbol. Shift up by 1 so (-1)
	// {@link Token//EOF} maps to {@code edges[0]}.
	this.edges = null;
	this.isAcceptState = false;
	// if accept state, what ttype do we match or alt do we predict?
	// This is set to {@link ATN//INVALID_ALT_NUMBER} when {@link
	// //predicates}{@code !=null} or
	// {@link //requiresFullContext}.
	this.prediction = 0;
	this.lexerActionExecutor = null;
	// Indicates that this state was created during SLL prediction that
	// discovered a conflict between the configurations in the state. Future
	// {@link ParserATNSimulator//execATN} invocations immediately jumped doing
	// full context prediction if this field is true.
	this.requiresFullContext = false;
	// During SLL parsing, this is a list of predicates associated with the
	// ATN configurations of the DFA state. When we have predicates,
	// {@link //requiresFullContext} is {@code false} since full context
	// prediction evaluates predicates
	// on-the-fly. If this is not null, then {@link //prediction} is
	// {@link ATN//INVALID_ALT_NUMBER}.
	//
	// <p>We only use these for non-{@link //requiresFullContext} but
	// conflicting states. That
	// means we know from the context (it's $ or we don't dip into outer
	// context) that it's an ambiguity not a conflict.</p>
	//
	// <p>This list is computed by {@link
	// ParserATNSimulator//predicateDFAState}.</p>
	this.predicates = null;
	return this;
}

// Get the set of all alts mentioned by all ATN configurations in this
// DFA state.
func (this *DFAState) getAltSet() {
	var alts = new Set();
	if (this.configs !== null) {
		for (var i = 0; i < this.configs.length; i++) {
			var c = this.configs[i];
			alts.add(c.alt);
		}
	}
	if (alts.length == 0) {
		return null;
	} else {
		return alts;
	}
}

// Two {@link DFAState} instances are equal if their ATN configuration sets
// are the same. This method is used to see if a state already exists.
//
// <p>Because the number of alternatives and number of ATN configurations are
// finite, there is a finite number of DFA states that can be processed.
// This is necessary to show that the algorithm terminates.</p>
//
// <p>Cannot test the DFA state numbers here because in
// {@link ParserATNSimulator//addDFAState} we need to know if any other state
// exists that has this exact set of ATN configurations. The
// {@link //stateNumber} is irrelevant.</p>
func (this *DFAState) equals(other) {
	// compare set of ATN configurations in this set with other
	if (this == other) {
		return true;
	} else if (!(other instanceof DFAState)) {
		return false;
	} else {
		return this.configs.equals(other.configs);
	}
}

func (this *DFAState) toString() {
	return "" + this.stateNumber + ":" + this.hashString();
}

func (this *DFAState) hashString() {
	return "" +  this.configs +
			(this.isAcceptState ?
					"=>" + (this.predicates !== null ?
								this.predicates :
								this.prediction) :
					"");
}

