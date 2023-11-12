// logical unicode constants
const AND    = "\u{2227}";
const OR     = "\u{2228}";
const NOT    = "\u{00AC}";
const IF     = "\u{21D2}";
const IFF    = "\u{21D4}";
const FORALL = "\u{2200}";
const EXISTS = "\u{2203}";
const TOP    = "\u{22A4}";
const BOT    = "\u{22A5}";

// arithmetic unicode constants
const TIMES  = "\u{00D7}";
const AST    = "\u{2217}";
const STAR   = "\u{22C6}";
const OPLUS  = "\u{2295}";
const OTIMES = "\u{2297}";
const NEG    = "\u{2212}";
const DIV    = "\u{00F7}";
const LE     = "\u{2264}";
const GE     = "\u{2265}";
const SIM    = "\u{223C}";
const CONG   = "\u{2245}";
const EQUIV  = "\u{2261}";

// set theory unicode constants
const IN        = "\u{2208}";
const CUP       = "\u{222A}";
const CAP       = "\u{2229}";
const SUBSET    = "\u{2282}";
const SUBSETEQ  = "\u{2286}";
const EMPTYSET  = "\u{2205}";
const NATURALS  = "\u{2115}";
const INTEGERS  = "\u{2124}";
const RATIONALS = "\u{211A}";
const REALS     = "\u{211D}";
const COMPLEX   = "\u{2102}";

// Greek letters
const LALPHA   = "\u{03B1}";
const LBETA    = "\u{03B2}";
const LGAMMA   = "\u{03B3}";
const LDELTA   = "\u{03B4}";
const LEPSILON = "\u{03B5}";
const LZETA    = "\u{03B6}";
const LETA     = "\u{03B7}";
const LTHETA   = "\u{03B8}";
const LLAMBDA  = "\u{03BB}";
const LMU      = "\u{03BC}";
const LXI      = "\u{03BE}";
const LPI      = "\u{03C0}";
const LRHO     = "\u{03C1}";
const LSIGMA   = "\u{03C3}";
const LTAU     = "\u{03C4}";
const LUPSILON = "\u{03C5}";
const LPHI     = "\u{03C6}";
const LVARPHI  = "\u{03D5}";
const LCHI     = "\u{03C7}";
const LPSI     = "\u{03C8}";
const LOMEGA   = "\u{03C9}";
const UGAMMA   = "\u{0393}";
const UDELTA   = "\u{0394}";
const UTHETA   = "\u{0398}";
const ULAMBDA  = "\u{039B}";
const UXI      = "\u{039E}";
const UPI      = "\u{03A0}";
const USIGMA   = "\u{03A3}";
const UPHI     = "\u{03A6}";
const UUPSILON = "\u{03A8}";
const UOMEGA   = "\u{03A9}";


// cvs is canvas element
// ctx is canvas context
const cvs = document.getElementById("canvas");
const ctx = cvs.getContext("2d");

// global variable declaration
var lastPoint      = {x: -1,
					  y: -1}; // last mouse point
var nodeSelectLoc  = -1;      // index of object being dragged
var dragging       = false;   // is object being dragged?
var newArrow       = false;   // is new arrow being made?
var panning        = false;   // is screen is being panned?
var nodes          = [];      // list of logic nodes
var nodesIdTable   = [];      // translation table that maps node ID to position in nodes
var settingsIndx   = -1;      // index of selected box, or -1
var settingsMenu   =  0;      // selected entry in settings menu
var settingsChild  =  0;      // selected child to be deleted
var settingsCursor =  0;      // cursor location when typing
var settingsClose  = false;   // settings menu close button is hovered
var recheckLogic   = false;   // recheck logic when true
var newNodePos     = 0;       // place to put new node
var cameraX        = 0;       // camera x position
var cameraY        = 0;       // camera y position

// constant delaration
const conradius  = 10;  // connector radius
const menuWidth  = 255; // settings menu width
const menuHeight = 130; // settings menu height

// inference rules
const infRules = ["",                // unselected
                  "Assume",          // assume
                  AND + " intro",    // and    intro
                  AND + " elim",     // and    elim
                  OR  + " intro",    // or     intro
                  OR  + " elim",     // or     elim
                  NOT + " intro",    // not    intro
                  NOT + " elim",     // not    elim
                  IF  + " intro",    // cond   intro
                  IF  + " elim",     // cond   elim
                  IFF + " intro",    // bicond intro
                  IFF + " elim",     // bicond elim
                  "= intro",         // equals intro
                  "= elim",          // equals elim
                  FORALL + " intro", // forall intro
                  FORALL + " elim",  // forall elim
                  EXISTS + " intro", // exists intro
                  EXISTS + " elim"]; // exists elim

// inference rules functions
// input is node, no output
// modifies node.valid, node.scope, and node.error
const infRulesFuncs = [(node) => {}, // null function
                       funcAssume,
                       funcAndIntro,
                       funcAndElim,
                       funcOrIntro,
                       funcOrElim,
                       funcNotIntro,
                       funcNotElim,
                       funcIfIntro,
                       funcIfElim,
                       funcIffIntro,
                       funcIffElim,
                       funcEqualsIntro,
                       funcEqualsElim,
                       funcForallIntro,
                       funcForallElim,
                       funcExistsIntro,
                       funcExistsElim];  

// error messages
const errMesgs = ["No error",
          /* 1*/  "Error: invalid formula",
          /* 2*/  "Error: empty formula",
          /* 3*/  "Error: missing identifier",
          /* 4*/  "Error: circular logic",
          /* 5*/  "Error: variable is already bound",
          /* 6*/  "Error: variable cannot be both bound and free",
          /* 7*/  "Error: no selected inference rule",
          /* 8*/  "Error: imvalid identifier",
          /* 9*/  "Error: too few arguments",
          /*10*/  "Error: missing input propositions",
          /*11*/  "Error: unmatched input propositions",
          /*12*/  "Error: assumptions cannot have inputs",
          /*13*/  "Error: conjunction is not introduced",
          /*14*/  "Error: conjunction is not eliminated",
          /*15*/  "Error: proposition is not found in conjunction",
          /*16*/  "Error: disjunction is not introduced",
          /*17*/  "Error: proposition is not found in disjunction",
          /*18*/  "Error: disjunction is not eliminated",
          /*19*/  "Error: proposition is not derived from case",
          /*20*/  "Error: negation is not introduced",
          /*21*/  "Error: input propositions are not a contradiction",
          /*22*/  "Error: negation of proposition is not in scope of inputs",
          /*23*/  "Error: negation is not eliminated",
          /*24*/  "Error: conditional is not introduced",
          /*25*/  "Error: input is not consequent of conditional",
          /*26*/  "Error: antecedent of conditional is not in scope of input",
          /*27*/  "Error: proposition is not consequent of conditional",
          /*28*/  "Error: input is not antecedent of conditional",
          /*29*/  "Error: conditional is not eliminated",
          /*30*/  "Error: biconditional is not introduced",
          /*31*/  "Error: biconditional is not eliminated",
          /*32*/  "Error: equality introduction cannot have inputs",
          /*33*/  "Error: equality is not introduced",
          /*34*/  "Error: propositions are not equal",
          /*35*/  "Error: equality is not eliminated",
          /*36*/  "Error: cannot equate bound variables",
          /*37*/  "Error: universal quantifier is not introduced",
          /*38*/  "Error: bound variable is present in input",
          /*39*/  "Error: proposition is not generalization of input",
          /*40*/  "Error: arbitrary variable generalized to multiple bound variables",
          /*41*/  "Error: arbitrary variable of input is present in proposition",
          /*42*/  "Error: arbitrary variable of input is free in scope of input",
          /*43*/  "Error: universal quantifier is not eliminated",
          /*44*/  "Error: input proposition has invalid quantifer form",
          /*45*/  "Error: bound variable is assigned several propositions",
          /*46*/  "Error: bound variable of input is free in proposition",
          /*47*/  "Error: bound variable is not assigned",
          /*48*/  "Error: cannot substitute bound variables",
          /*49*/  "Error: unassigned bound variables"];
				  

// set canvas size to window size
cvs.width  = window.innerWidth;
cvs.height = window.innerHeight - 56;

// update canvas window size on window size change
window.addEventListener("resize", function(event) {
	cvs.width  = window.innerWidth;
	cvs.height = window.innerHeight - 56;
	draw();
});

// canvas event listeners
// TODO: dragging can only be left click
cvs.addEventListener("mousemove", moveHandler);
cvs.addEventListener("mousedown", mouseDownHandler);
cvs.addEventListener("mouseup"  , mouseUpHandler);
cvs.addEventListener("keydown"  , keyDownHandler);

// menu bar button actions
document.getElementById("new node").addEventListener("click", newNode);
document.getElementById("check"   ).addEventListener("click", recheck);

// Well Formed Formula class
class WFFClass {
	// WFFClass constructor
	constructor() {
		this.name = ""; // WFF formula name
		this.args = []; // WFF arguments
		this.type =  0; // what type is WFF
		this.free = []; // free variables
		this.bnda = []; // bound above variables
		this.bndb = []; // bound below variables
		
		// types
		// 0 special
		// 1 atomic
		// 2 function
		// 3 unary operator
		// 4 n-ary operator
		// 5 quantifier
	}
	
	// WFFClass recursive print method
	// returns string
	print() {
		var backUp = false; // true if case gets unhit somehow
		
		if (this.name == "") return "()";      // WFF is empty
		if (this.type == 0) { // test for special characters
			if (this.name == "emptyset") {
				return EMPTYSET;
			} else if (this.name == "top") {
				return TOP;
			} else if (this.name == "bot") {
				return BOT;
			} else if (this.name == "N") {
				return NATURALS;
			} else if (this.name == "Z") {
				return INTEGERS;
			} else if (this.name == "Q") {
				return RATIONALS;
			} else if (this.name == "R") {
				return REALS;
			} else if (this.name == "C") {
				return COMPLEX;
			} else if (this.name == "alpha") {
				return LALPHA;
			} else if (this.name == "beta") {
				return LBETA;
			} else if (this.name == "gamma") {
				return LGAMMA;
			} else if (this.name == "delta") {
				return LDELTA;
			} else if (this.name == "epsilon") {
				return LEPSILON;
			} else if (this.name == "zeta") {
				return LZETA;
			} else if (this.name == "eta") {
				return LETA;
			} else if (this.name == "theta") {
				return LTHETA;
			} else if (this.name == "lambda") {
				return LLAMBDA;
			} else if (this.name == "mu") {
				return LMU;
			} else if (this.name == "xi") {
				return LXI;
			} else if (this.name == "pi") {
				return LPI;
			} else if (this.name == "rho") {
				return LRHO;
			} else if (this.name == "sigma") {
				return LSIGMA;
			} else if (this.name == "tau") {
				return LTAU;
			} else if (this.name == "upsilon") {
				return LUPSILON;
			} else if (this.name == "phi") {
				return LPHI;
			} else if (this.name == "varphi") {
				return LVARPHI;
			} else if (this.name == "chi") {
				return LCHI;
			} else if (this.name == "psi") {
				return LPSI;
			} else if (this.name == "Omega") {
				return LOMEGA;
			} else if (this.name == "Gamma") {
				return UGAMMA;
			} else if (this.name == "Delta") {
				return UDELTA;
			} else if (this.name == "Theta") {
				return UTHETA;
			} else if (this.name == "Lambda") {
				return ULAMBDA;
			} else if (this.name == "Xi") {
				return UXI;
			} else if (this.name == "Pi") {
				return UPI;
			} else if (this.name == "Sigma") {
				return USIGMA;
			} else if (this.name == "Phi") {
				return UPHI;
			} else if (this.name == "Upsilon") {
				return UUPSILON;
			} else if (this.name == "Omega") {
				return UOMEGA;
			} else return this.name;
		}
		if (this.type == 1) return this.name; // atomic
		if (this.type == 3) { // unary
			if (this.name == "not" || this.name == "-") { // not or neg
				// spacer character
				var spacer = "";
				
				if (this.name == "not") spacer = NOT;
				if (this.name == "-")   spacer = NEG;
				
				if (this.type >= this.args[0].type) { // argument is of equal or lower type
					return spacer + this.args[0].print();
				} else if (this.args[0].type == 5) { // argument is quantifier
					return spacer + this.args[0].print();
				} else { // argument is of higher type and not quantifier
					return spacer + "(" + this.args[0].print() + ")";
				}
			} else backUp = true; // back up case
		}
		if (this.type == 4) { // n-ary
			var check = false; // check if name is any of options
			var spacer = ""; // spacer character
			
			// assign correct spacer character and mark that name is the correct type
			if (this.name == "and"     ) {check = true; spacer = AND;}
			if (this.name == "or"      ) {check = true; spacer = OR;}
			if (this.name == "="       ) {check = true; spacer = "=";}
			if (this.name == "+"       ) {check = true; spacer = "+";}
			if (this.name == "-"       ) {check = true; spacer = NEG;}
			if (this.name == "*"       ) {check = true; spacer = "*";}
			if (this.name == "times"   ) {check = true; spacer = TIMES;}
			if (this.name == "ast"     ) {check = true; spacer = AST;}
			if (this.name == "star"    ) {check = true; spacer = STAR;}
			if (this.name == "~"       ) {check = true; spacer = SIM;}
			if (this.name == "sim"     ) {check = true; spacer = SIM;}
			if (this.name == "cong"    ) {check = true; spacer = CONG;}
			if (this.name == "equiv"   ) {check = true; spacer = EQUIV;}
			if (this.name == "oplus"   ) {check = true; spacer = OPLUS;}
			if (this.name == "otimes"  ) {check = true; spacer = OTIMES;}
			if (this.name == "|"       ) {check = true; spacer = "|";}
			if (this.name == "div"     ) {check = true; spacer = DIV;}
			if (this.name == "<"       ) {check = true; spacer = "<";}
			if (this.name == ">"       ) {check = true; spacer = ">";}
			if (this.name == "le"      ) {check = true; spacer = LE;}
			if (this.name == "ge"      ) {check = true; spacer = GE;}
			if (this.name == "in"      ) {check = true; spacer = IN;}
			if (this.name == "cup"     ) {check = true; spacer = CUP;}
			if (this.name == "cap"     ) {check = true; spacer = CAP;}
			if (this.name == "subset"  ) {check = true; spacer = SUBSET;}
			if (this.name == "subseteq") {check = true; spacer = SUBSETEQ;}
			
			if (check) {
				var prt = []; // array of string form of arguments
				// loop over arguments
				for (var i = 0; i < this.args.length; i++) {
					// check if argument is of lower type
					if (this.type > this.args[i].type) {
						// push string form of argument
						prt.push(this.args[i].print());
					} else {
						// push string form of argument with surrounding parens
						prt.push("(" + this.args[i].print() + ")");
					}
				}
				
				// print
				return prt.join(spacer);
			} else if (this.name == "if" || this.name == "iff") { // if, iff
				// antecedent and consequent string form
				var antecedent = this.args[0].print();
				var consequent = this.args[1].print();
				
				// add surrounding parens when one is of higher or equal type
				if (this.type <= this.args[0].type) antecedent = "(" + antecedent + ")";
				if (this.type <= this.args[1].type) consequent = "(" + consequent + ")";
				
				var spacer = ""; // spacer character
				
				// assign correct spacer character
				if (this.name == "if" ) spacer = IF;
				if (this.name == "iff") spacer = IFF;
				
				// print
				return antecedent + spacer + consequent;
			} else backUp = true; // back up case
		}
		if (this.type == 5) { // quantifier
			if (this.name == "forall" || this.name == "exists") { // forall
				var prt = []; // array of string form of arguments
				for (var i = 0; i < this.args.length - 1; i++) {
					// push string form of argument
					prt.push(this.args[i].print());
				}
				
				var spacer = ""; // spacer character
				
				// assign correct spacer character
				if (this.name == "forall") spacer = FORALL;
				if (this.name == "exists") spacer = EXISTS;
				
				// print
				if (this.args[this.args.length-1].type == 5) { // no parenthesis with nested quantifiers
					return spacer + prt.join(",") + this.args[this.args.length-1].print();
				} else { // argument is not quantifier
					return spacer + prt.join(",") + "(" + this.args[this.args.length-1].print() + ")";
				}
			}
		}
		
		if (this.type == 2 || backUp) { // function
			// function name
			var name = this.name;
			
			// update name with special function names
			if (this.name == "alpha")   name = LALPHA;
			if (this.name == "beta")    name = LBETA;
			if (this.name == "gamma")   name = LGAMMA;
			if (this.name == "delta")   name = LDELTA;
			if (this.name == "epsilon") name = LEPSILON;
			if (this.name == "zeta")    name = LZETA;
			if (this.name == "eta")     name = LETA;
			if (this.name == "theta")   name = LTHETA;
			if (this.name == "lambda")  name = LLAMBDA;
			if (this.name == "mu")      name = LMU;
			if (this.name == "xi")      name = LXI;
			if (this.name == "pi")      name = LPI;
			if (this.name == "rho")     name = LRHO;
			if (this.name == "sigma")   name = LSIGMA;
			if (this.name == "tau")     name = LTAU;
			if (this.name == "upsilon") name = LUPSILON;
			if (this.name == "phi")     name = LPHI;
			if (this.name == "varphi")  name = LVARPHI;
			if (this.name == "chi")     name = LCHI;
			if (this.name == "psi")     name = LPSI;
			if (this.name == "omega")   name = LOMEGA;
			if (this.name == "Gamma")   name = UGAMMA;
			if (this.name == "Delta")   name = UDELTA;
			if (this.name == "Theta")   name = UTHETA;
			if (this.name == "Lambda")  name = ULAMBDA;
			if (this.name == "Xi")      name = UXI;
			if (this.name == "Pi")      name = UPI;
			if (this.name == "Sigma")   name = USIGMA;
			if (this.name == "Phi")     name = UPHI    
			if (this.name == "Upsilon") name = UUPSILON;
			if (this.name == "Omega")   name = UOMEGA;
			
			var prt = []; // array of string form of arguments
			// loop over arguments
			for (var i = 0; i < this.args.length; i++) {
				prt.push(this.args[i].print()); // push string form of argument
			}
			return name + "(" + prt.join(", ") + ")";
		}
		
		return "none"; // back up case
	}
	
	// determine if two WFFs are equal
	equals(WFF) {
		// check if names match
		if (this.name != WFF.name) return false;
		
		// check if length of arguments are equal
		if (this.args.length != WFF.args.length) return false;
		
		// loop over arguments and compare
		// order matters
		for (var i = 0; i < this.args.length; i++) {
			// check if individual arguments are equal
			if (!this.args[i].equals(WFF.args[i])) return false;
		}
		
		// WFFs are equal
		return true;
	}
	
	// determine if two WFFs are equal up to the given equality
	// used for equality elimination
	equalsElim(WFF, E) {
		// check for base equality
		if (this.equals(WFF)) return true;
		
		var flag1 = false; // is this argument of E?
		var flag2 = false; // is WFF  argument of E?
		
		// check for equality with each term in equals
		for (var i = 0; i < E.args.length; i++) {
			if (E.args[i].equals(this)) flag1 = true;
			if (E.args[i].equals(WFF))  flag2 = true;
		}
		
		// check for direct substitution
		if (flag1 && flag2) return true;
		
		// check if names match
		if (this.name != WFF.name) return false;
		
		// check if length of raguments are equal
		if (this.args.length != WFF.args.length) return false;
		
		// loop over arguments and compare
		// order matters
		for (var i = 0; i < this.args.length; i++) {
			// check if individual arguments are equal
			if (!this.args[i].equalsElim(WFF.args[i], E)) return false;
		}
		
		// WFFs are equal
		return true;
	}
	
	// determine if two WFFs are equal up to substitution of variables
	// modify pairs by appending all variable substitution pairs
	// used for universal quantifier introduction
	forallIntro(WFF, pairs) {
		// check if names match
		if (this.name != WFF.name) {
			// check if both WFFs are atomic or special
			if ((this.type < 2) && (WFF.type < 2)) {
				// push pair if so
				pairs.push([this.name, WFF.name]);
			} else return false; // formulas are not substitues if not
		}
		
		// check if length of arguments are equal
		if (this.args.length != WFF.args.length) return false;
		
		// loop over arguments and compare
		// order matters
		for (var i = 0; i < this.args.length; i++) {
			// check if individual arguments are equal
			if (!this.args[i].forallIntro(WFF.args[i], pairs)) return false;
		}
		
		// WFFs are equal
		return true;
	}
	
	// determine if two WFFs are equal up to substitution of atoms with propositions
	// WFF is parent
	// return error ID
	forallElim(WFF, pairs) {
		// check if parent WFF type is atomic or special
		if (WFF.type < 2) {
			// check if parent WFF is a bound variable
			
			// match has been made
			var match = false;
			
			// loop over pairs
			for (var i = 0; i < pairs.length; i++) {
				if (pairs[i][0] == WFF.name) {
					match = true; // match has been made
					
					// check if substituion has not been marked
					if (pairs[i][1] == -1) {
						// mark substitution
						pairs[i][1] = this;
						
						// exit for loop
						break;
					} else if (!this.equals(pairs[i][1])) { // second substitution is made
						return 45; // invalid substitution is made
					}
				}
			}
			
			// check if no match has been made and WFFs are not equal
			if (!match && !WFF.equals(this)) {
				return 34; // propositions are not equal
			} 
			
			// match has been made
			return 0;
			
			// else check if names differ
		} else if (this.name != WFF.name) {
			return 34; // propositions are not equal
		}
		
		// check if length of arguments are equal
		if (this.args.length != WFF.args.length) return 34; // propositions are not equal
		
		// loop over arguments and compare
		// order matters
		for (var i = 0; i < WFF.args.length; i++) {
			// check if individual arguments are equal
			var check = this.args[i].forallElim(WFF.args[i], pairs);
			
			if (check != 0) return check;
		}
		
		// WFFs are equal
		return 0;
	}
	
	// check if WFF contains atom
	contains(atom) {
		// check if WFF is atomic or special with name atom
		if ((this.type < 2) && (this.name == atom)) return true;
		
		// loop over arguments
		for (var i = 0; i < this.args.length; i++) {
			// check if argument contains atom
			if (this.args[i].contains(atom)) return true;
		}
		
		// WFF does not contain atom
		return false;
	}
	
	// determine which variable are bound or free
	bindVars() {
		if (this.type < 2) { // WFF is atomic or special
			if (!this.bnda.includes(this.name)) { // check if variable is not bound from above
				this.free.push(this.name); // variable is free
			}
		} else if (2 <= this.type && this.type <= 4) { // check if WFF is function or operation	
			// loop over arguments
			for (var i = 0; i < this.args.length; i++) {
				// argument inherits bound above variables of WFF
				this.args[i].bnda = this.bnda;
				
				// determine variable bind types of argument
				this.args[i].bindVars();
				
				// push up bound below and free variables
				this.bndb = this.bndb.concat(this.args[i].bndb);
				this.free = this.free.concat(this.args[i].free);
			}
			
			// remove duplicates in free and bound below variables
			this.bndb = [...new Set(this.bndb)];
			this.free = [...new Set(this.free)];
		} else if (this.type == 5) { // check if WFF is quantifier
			// loop over variables
			for (var i = 0; i < this.args.length - 1; i++) {
				// push variables as bound below
				this.bndb.push(this.args[i].name);
			}
			
			// WFF argument
			var WFF = this.args[this.args.length - 1];
			
			// inherit bound abve and below variables
			WFF.bnda = this.bnda.concat(this.bndb);
			
			// determine variable bind types of argument
			WFF.bindVars();
				
			// push up bound below and free variables
			this.bndb = this.bndb.concat(WFF.bndb);
			this.free = this.free.concat(WFF.free);
			
		}
	}
	
	// unbinds variables in WFF tree
	unbindVars() {
		// unbind variables
		this.bnda = [];
		this.bndb = [];
		this.free = [];
		
		// loop over arguments
		for (var i = 0; i < this.args.length; i++) {
			this.args[i].unbindVars();
		}
	}
}

// node class
class nodeClass {
	// nodeClass constructor
	constructor() {
		this.name    = ""; // node name
		this.formula = ""; // WFF (Well-Formed Formula) in string form
		this.infRule =  0; // inference rule
		
		this.WFFTree = new WFFClass(); // WFF tree structure
		
		this.id    =  0;   // node id
		this.latex = "";   // formula written in unicode
		
		this.scope    = []; // node dependencies
		this.children = []; // children
		this.parents  = []; // parents
		
		this.valid = false; // is inference valid?
		this.error = 2;     // error message index
		this.hover = false; // is mouse over settings button?
		
		this.width  = 50    // node width radius
		this.height = 50;   // node height radius
		
		this.x = 100;        // node x position
		this.y = 100;        // node y position
	}
}

// handler for mouse down event
function mouseDownHandler(e) {
	// obtain x and y position inside canvas
	var x = e.pageX - e.target.offsetLeft;
	var y = e.pageY - e.target.offsetTop;
	
	// close settings menu when clicked outide or closed
	var wcheck1 = Math.abs(cvs.width  / 2 - x) >= menuWidth ;
	var hcheck1 = Math.abs(cvs.height / 2 - y) >= menuHeight;
	var wcheck2 = Math.abs(cvs.width  / 2 - menuWidth  + 15 - x) < 10;
	var hcheck2 = Math.abs(cvs.height / 2 - menuHeight + 15 - y) < 10;
	
	// menu is closed
	if ((wcheck2 && hcheck2) || wcheck1 || hcheck1) {
		settingsIndx  = -1;
		settingsMenu  =  1;
		settingsChild =  0;
		
		// run if logic needs to be rechecked
		if (recheckLogic) {
			update();
		}
	}
	
	// loop over nodes and check if box is selected
	// then check if settings button is selected
	// skip if settings menu is open
	if (settingsIndx == -1) {
		for (var i = nodes.length-1; i >= 0; i--) {
			var node = nodes[i];
			
			// node relative coordinates
			var nX = node.x - cameraX;
			var nY = node.y - cameraY;
			
			// mouse inside box
			var wcheck1 = Math.abs(nX-x) < node.width ;
			var hcheck1 = Math.abs(nY-y) < node.height;
			
			// mouse inside settings button
			var wcheck2 = Math.abs(nX + node.width  - 15 - x) < 10;
			var hcheck2 = Math.abs(nY + node.height - 15 - y) < 10;
			
			// distance between mouse and center of output circle
			var xdis = nX - x;
			var ydis = nY - y + node.height + conradius;
			
			// is mouse inside any of the three elements?
			var bool1 = wcheck1 && hcheck1;
			var bool2 = wcheck2 && hcheck2;
			var bool3 = Math.sqrt(xdis**2 + ydis**2) <= conradius;
			
			// check if output circle is selected
			if (bool3) {
				newArrow = true;
				lastPoint.x   = x;
				lastPoint.y   = y;
				nodeSelectLoc = i;
				break;
			}
			
			// check if settings button is selected
			if (bool2) {
				nodeSelectLoc = i;
				settingsIndx  = nodes.length - 1;
				break;
			}
			
			// check if box is selected
			if (bool1) {
				dragging = true;
				lastPoint.x   = x;
				lastPoint.y   = y;
				nodeSelectLoc = i;
				break;
			}
		}
	
		// if node is selected, push it to the top
		if (dragging || newArrow || (settingsIndx != -1)) {
			// push node to top
			nodes.splice(nodes.length, 0, nodes[nodeSelectLoc]);
			nodes.splice(nodeSelectLoc, 1);
			
			// update ID translation table
			for (var i = 0; i < nodes.length; i++) {
				if (nodesIdTable[i] == nodeSelectLoc) {
					nodesIdTable[i] = nodes.length - 1;
				} else if (nodesIdTable[i] > nodeSelectLoc) {
					nodesIdTable[i] -= 1;
				}
			}
			
			// update nodeSelectLoc
			nodeSelectLoc = nodes.length - 1
		}
	}
	
	if ((settingsIndx == -1) && !dragging && !newArrow) {
		// update last point and draw
		lastPoint.x = x;
		lastPoint.y = y;
		
		panning = true;
		
	}
}

// handler for mouse up event
function mouseUpHandler(e) {
	// check if arrow is being drawn
	if (newArrow) {
		newArrow = false; // reuse of variable for when arrow can be made
		// loop over nodes to check output arrow
		for (var i = 0; i < nodes.length; i++) {
			var node = nodes[i];
			
			var xdis = node.x - cameraX - lastPoint.x;
			var ydis = node.y - cameraY - lastPoint.y - node.height - conradius;
			// if arrow is dropped onto input circle, note node id.
			if (Math.sqrt(xdis**2 + ydis**2) <= conradius) {
				newArrow = true;
				var nodeOutputLoc = i;
			}
		}
		// if new arrow can be made and no immediate loop is made, continue
		if (newArrow && (nodeOutputLoc != nodeSelectLoc)) {
			// check if new node does not exist as child of old node
			if (!(nodes[nodeSelectLoc].children.includes(nodes[nodeOutputLoc].id))) {
				// new node is child of old node
				// old node is parent of new node
				nodes[nodeSelectLoc].children.push(nodes[nodeOutputLoc].id);
				nodes[nodeOutputLoc].parents.push(nodes[nodeSelectLoc].id);
				
				// sort lists
				nodes[nodeSelectLoc].children.sort();
				nodes[nodeOutputLoc].parents.sort();
				
				// recheck logic
				update();
			}
		}
	}
	
	// reset markers
	newArrow = false;
	dragging = false;
	panning  = false;
	
	// invalidate data
	lastPoint.x = -1;
	lastPoint.y = -1;
	nodeSelectLoc = -1;
	
	// redraw screen
	// useful for removing unattached arrows
	draw();
}

// handler for mouse movement event
function moveHandler(e) {
	// obtain x and y position inside canvas
	var x = e.pageX - e.target.offsetLeft;
	var y = e.pageY - e.target.offsetTop;
	
	// check if box is being dragged
	if (dragging) {
		// change in mouse position
		var deltaX = x - lastPoint.x;
		var deltaY = y - lastPoint.y;

		var node = nodes[nodeSelectLoc];
		
		// update node position
		node.x += deltaX;
		node.y += deltaY;
		
		// bound node position from left and top
		// node.x = Math.max(node.x, node.width  + 2);
		// node.y = Math.max(node.y, node.height + 2 + 2 * conradius);
		
		// bound node position from right and bottom
		// node.x = Math.min(node.x, window.innerWidth  - node.width  - 2);
		// node.y = Math.min(node.y, window.innerHeight - node.height - 2 - 2 * conradius);
		
		// update last node position
		lastPoint.x = x;
		lastPoint.y = y;
	}
	
	// check if new arrow is being made
	if (newArrow) {
		// update last point and draw
		lastPoint.x = x;
		lastPoint.y = y;
	}
	
	if (panning) {
		// change in mouse position
		var deltaX = x - lastPoint.x;
		var deltaY = y - lastPoint.y;
		
		// update camera position
		cameraX -= deltaX;
		cameraY -= deltaY;
		
		// update last point and draw
		lastPoint.x = x;
		lastPoint.y = y;
	}
	
	// check if mouse is over settings button unobstructed
	
	var hoverLoc = -1; // node with selected settings button
	
	// loop over nodes
	for (var i = 0; i < nodes.length; i++) {
		var node = nodes[i];
		
		// node relative coordinates
		var nX = node.x - cameraX;
		var nY = node.y - cameraY;
		
		node.hover = false; // reset hover
		
		// check if box is selected
		var wcheck1 = Math.abs(nX-x) < node.width ;
		var hcheck1 = Math.abs(nY-y) < node.height;
		
		// distance between mouse and center of input/output circle
		var xdis  = nX - x;
		var ydis1 = nY + node.height + conradius - y;
		var ydis2 = nY - node.height - conradius - y;
		
		// is mouse inside any of the three elements?
		var bool1 = wcheck1 && hcheck1;
		var bool2 = Math.sqrt(xdis**2 + ydis1**2) <= conradius;
		var bool3 = Math.sqrt(xdis**2 + ydis2**2) <= conradius;
		
		// any potential settings button is obstructed by node
		if (bool1 || bool2 || bool3) hoverLoc = -1;
		
		// check if new settings button is selected
		wcheck2 = Math.abs(nX + node.width  - 15 - x) < 10;
		hcheck2 = Math.abs(nY + node.height - 15 - y) < 10
		
		// settings button is selected
		if (wcheck2 && hcheck2) hoverLoc = i;
		
		// check if menu is active and selected
		var wcheck3 = Math.abs(cvs.width  / 2 - x) <= menuWidth ;
		var hcheck3 = Math.abs(cvs.height / 2 - y) <= menuHeight;
		
		// mouse is inside active menu
		if (wcheck3 && hcheck3 && (settingsIndx >= 0)) hoverLoc = -1;
	}
	
	// check if settings button is selected
	if (hoverLoc != -1) nodes[hoverLoc].hover = true;
	
	// check if settings menu close button is selected
	var wcheck = Math.abs(cvs.width  / 2 - menuWidth  + 15 - x) < 10;
	var hcheck = Math.abs(cvs.height / 2 - menuHeight + 15 - y) < 10;
	settingsClose = wcheck && hcheck;
	
	// redraw scene
	draw();
}

// handler for keyboard down event
function keyDownHandler(e) {
	if(["Space","ArrowUp","ArrowDown","ArrowLeft","ArrowRight"].indexOf(e.code) > -1) {
        e.preventDefault();
    }
	
	// check if menu is active
	if (settingsIndx >= 0) {
		var node = nodes[settingsIndx];
		
		// move menu selector arrow up or down
		if (e.key == "ArrowUp"  ) {
			settingsMenu  -= 1;
			settingsCursor = 0;
			
			// send cursor to end of string
			if (settingsMenu == 1) settingsCursor = node.name.length;
			if (settingsMenu == 2) settingsCursor = node.formula.length;
		}
		if (e.key == "ArrowDown") {
			settingsMenu  += 1;
			settingsCursor = 0;
			
			// send cursor to end f string
			if (settingsMenu == 1) settingsCursor = node.name.length;
			if (settingsMenu == 2) settingsCursor = node.formula.length;
		}
		
		// bound menu selector arrow position
		if (settingsMenu < 0) settingsMenu = 3 + Math.sign(node.children.length);
		if ((settingsMenu > 3) && (node.children.length == 0)) settingsMenu = 0;
		if ((settingsMenu > 4) && (node.children.length > 0))  settingsMenu = 0;
		
		// move typing cursor left
		if ((1 <= settingsMenu <= 2) && (e.key == "ArrowLeft")) {
			settingsCursor = Math.max(0, settingsCursor - 1);
		}
		
		// move typing cursor right
		if ((settingsMenu == 1) && (e.key == "ArrowRight")) {
			settingsCursor = Math.min(node.name.length, settingsCursor + 1);
		}
		
		// move typing cursor right
		if ((settingsMenu == 2) && (e.key == "ArrowRight")) {
			settingsCursor = Math.min(node.formula.length, settingsCursor + 1);
		}
		
		// type to node name
		if ((settingsMenu == 1) && (e.key.length == 1)) {
			node.name  = node.name.slice(0, settingsCursor) + e.key + node.name.slice(settingsCursor);
			settingsCursor += 1;
		}
		
		// type to node formula
		if ((settingsMenu == 2) && (e.key.length == 1)) {
			node.formula = node.formula.slice(0, settingsCursor) + e.key + node.formula.slice(settingsCursor);
			recheckLogic = true;
			settingsCursor += 1;
		}
		
		// delete char from node name at cursor
		if ((settingsMenu == 1) && (e.key == "Delete")) {
			node.name = node.name.slice(0, settingsCursor) + node.name.slice(settingsCursor+1);
		}
		
		// delete char from node formula at cursor
		if ((settingsMenu == 2) && (e.key == "Delete")) {
			node.formula = node.formula.slice(0, settingsCursor) + node.formula.slice(settingsCursor+1);
		}
		
		// remove char from node name at cursor
		if ((settingsMenu == 1) && (e.key == "Backspace")) {
			node.name = node.name.slice(0, Math.max(0, settingsCursor-1)) + node.name.slice(settingsCursor);
			settingsCursor = Math.max(0, settingsCursor - 1);
		}
		
		// remove char from node formula at cursor
		if ((settingsMenu == 2) && (e.key == "Backspace")) {
			node.formula = node.formula.slice(0, Math.max(0, settingsCursor-1)) + node.formula.slice(settingsCursor);
			settingsCursor = Math.max(0, settingsCursor - 1);
			recheckLogic = true;
		}
		
		// cycle inference rules up
		if ((settingsMenu == 3) && (e.key == "ArrowLeft")) {
			node.infRule -= 1;
			if (node.infRule < 0) node.infRule = infRules.length - 1;
			recheckLogic = true;
		}
		
		// cycle inference rules up
		if ((settingsMenu == 3) && (e.key == "ArrowRight")) {
			node.infRule += 1;
			if (node.infRule >= infRules.length) node.infRule = 0;
			recheckLogic = true;
		}
		
		// cycle children down
		if ((settingsMenu == 4) && (e.key == "ArrowLeft")) {
			settingsChild -= 1;
			if (settingsChild < 0) settingsChild = node.children.length - 1;
		}
		
		// cycle children down
		if ((settingsMenu == 4) && (e.key == "ArrowRight")) {
			settingsChild += 1;
			if (settingsChild >= node.children.length) settingsChild = 0;
		}
		
		// delete child
		if ((settingsMenu == 4) && (e.key == "Enter")) {
			// remove node from parent list of child
			var parents = nodes[nodesIdTable[node.children[settingsChild]]].parents;
			parents.splice(parents.indexOf(node.id), 1);
			
			// remove child from child list of node
			node.children.splice(settingsChild, 1);
			
			// cap settingsChild after child removal
			settingsChild = Math.min(settingsChild, node.children.length - 1);
			
			// move menu selector arrow up if last child is removed
			if (node.children.length == 0) settingsMenu = 3;
			
			recheckLogic = true;
		}
		
		// delete node
		if ((settingsMenu == 0) && (e.key == "Enter")) {
			// loop over nodes and update/remove children
			for (var i = 0; i < nodes.length; i++) {
				// copy of parents and children
				var nodeParents  = nodes[i].parents;
				var nodeChildren = nodes[i].children;
				
				// reset node children
				nodes[i].parents  = [];
				nodes[i].children = [];
				
				// loop over parents and add modified parents IDs
				for (var j = 0; j < nodeParents.length; j++) {
					// parent ID below removed node ID
					if (nodeParents[j] < node.id) {
						nodes[i].parents.push(nodeParents[j]);
					}
					
					// parent ID above removed node ID
					if (nodeParents[j] > node.id) {
						nodes[i].parents.push(nodeParents[j]-1);
					}
				}
				
				// loop over children and add modified children IDs
				for (var j = 0; j < nodeChildren.length; j++) {
					// child ID below removed node ID
					if (nodeChildren[j] < node.id) {
						nodes[i].children.push(nodeChildren[j]);
					}
					
					// child ID above removed node ID
					if (nodeChildren[j] > node.id) {
						nodes[i].children.push(nodeChildren[j]-1);
					}
				}
			}
			
			// cut node from nodes and nodesIdTable
			nodes.splice(settingsIndx, 1);
			nodesIdTable.splice(node.id, 1);
			
			// update both arrays
			for (var i = 0; i < nodes.length; i++) {
				if (nodes[i].id > node.id) nodes[i].id -= 1;
				if (nodesIdTable[i] > settingsIndx) nodesIdTable[i] -= 1;
			}
			
			// reset settings variables
			settingsChild =  0;
			settingsIndx  = -1;
			
			// recheck logic flag
			recheckLogic = true;
		}
	}
	
	// recheck scene
	update();
	
	// redraw scene
	draw();
}

// new node action
function newNode(e) {
	// create new node
	node = new nodeClass();
	
	// position new node
	node.x = 70 + 25 * newNodePos + cameraX;
	node.y = 70 + 25 * newNodePos + cameraY;
	
	// set node id
	node.id = nodes.length;
	
	// set default dependency list
	node.scope.push(node.id);
	
	// increment and loop newNodePos
	newNodePos += 1
	if (newNodePos > 4) newNodePos = 0;
	
	// update nodes and nodesIdTable
	nodes.push(node);
	nodesIdTable.push(nodesIdTable.length);
	
	// redraw scene
	draw();
}

// screen draw function
function draw() {
	// clear screen
	ctx.clearRect(0, 0, cvs.width, cvs.height);
	
	// apply stroke and fill styles
	ctx.strokeStyle = "#000000";
	ctx.fillStyle   = "#AAAAAA";
	
	// draw new arrow
	// check if new arrow is being drawn
	if (newArrow) {
		// draw arrow from output circle of node
		node = nodes[nodeSelectLoc];
		
		// node relative coordinates
		var nX = node.x - cameraX;
		var nY = node.y - cameraY;
		
		ctx.beginPath();
		// begin bezier at output circle
		ctx.moveTo(nX, nY + node.height + conradius);
		// control points lie 200 units below output circle and 200 units above end point
		ctx.bezierCurveTo(nX, nY + node.height + conradius + 200,
						  lastPoint.x, lastPoint.y - 200,
						  lastPoint.x, lastPoint.y);
		ctx.stroke();
	}
	
	// draw arrows
	// loop over nodes
	for (var i = 0; i < nodes.length; i++) {
		var node1 = nodes[i];
		
		// node 1 relative coordinates
		var n1X = node1.x - cameraX;
		var n1Y = node1.y - cameraY;
		
		// loop over children
		for (var j = 0; j < node1.children.length; j++) {
			var node2 = nodes[nodesIdTable[node1.children[j]]];
		
			// node 2 relative coordinates
			var n2X = node2.x - cameraX;
			var n2Y = node2.y - cameraY;
			
			// draw bezier from output circle of parent to input circle of child
			ctx.beginPath();
			// begin bezier at output circle
			ctx.moveTo(n1X, n1Y + node1.height + conradius);
			// control points lie 200 units below output circle and 200 units above input circle
			ctx.bezierCurveTo(n1X, n1Y + node1.height + conradius + 200,
							  n2X, n2Y - node2.height - conradius - 200,
							  n2X, n2Y - node2.height - conradius);
			ctx.stroke();
		}
	}
	
	// draw node boxes
	// loop over nodes
	for (var i = 0; i < nodes.length; i++) {
		node = nodes[i];
		
		// node relative coordinates
		var nX = node.x - cameraX;
		var nY = node.y - cameraY;
		
		// draw rectangle centered at (x,y)
		// width and height are twice of node.width and node.height
		ctx.beginPath();
		ctx.roundRect(nX-node.width,
					  nY-node.height,
					  2 * node.width,
					  2 * node.height,
					  10);
		ctx.fill();
		ctx.stroke();
		
		// draw output circle
		ctx.beginPath();
		ctx.arc(nX, nY + node.height + conradius,
				conradius, 0, 2 * Math.PI);
		ctx.fill();
		ctx.stroke();
		
		// draw input circle
		ctx.beginPath();
		ctx.arc(nX, nY - node.height - conradius,
				conradius, 0, 2 * Math.PI);
		ctx.fill();
		ctx.stroke();
		
		// apply text fonts and styles
		ctx.font         = "16px Arial";
		ctx.fillStyle    = "#000000";
		ctx.textAlign    = "center";
		ctx.textBaseline = "middle";
		
		// draw enter text
		ctx.fillText(node.name,              nX, nY - 15);
		ctx.fillText(node.latex,             nX, nY);
		ctx.fillText(infRules[node.infRule], nX, nY + 15);
		
		// reset text alignment
		ctx.textAlign    = "start";
		ctx.textBaseline = "alphabetic";
		
		// draw id and dependency list
		ctx.fillText(node.id,
					 nX - node.width  + 5,
					 nY - node.height + 18);
		ctx.fillText("{" + node.scope.join(", ") + "}",
					 nX - node.width  + 5,
					 nY + node.height - 10);
		
		// draw validity check / mark
		if (node.valid) {
			ctx.fillStyle = "#00FF00";
			ctx.fillText("\u{2714}", nX - 5 + node.width - ctx.measureText("\u{2714}").width, nY - node.height + 18);
		} else {
			ctx.fillStyle = "#FF0000";
			ctx.fillText("\u{2718}", nX - 5 + node.width - ctx.measureText("\u{2718}").width, nY - node.height + 18);
			
		}
		
		// settings button fill styles
		if (node.hover) {
			ctx.fillStyle = "#AAAAAA";
		} else {
			ctx.fillStyle = "#777777";
		}
		
		// draw settings button
		ctx.beginPath();
		ctx.roundRect(nX + node.width  - 5,
					  nY + node.height - 5,
					  -20, -20, 2);
		ctx.fill();
		ctx.stroke();
		
		// settings button decal styles
		ctx.fillStyle = "#000000";
		ctx.lineWidth = 2;
		
		// spoke size and gear positions
		var a = 8;
		var b = a / Math.sqrt(2);
		var w = nX + node.width  - 15;
		var h = nY + node.height - 15;
		
		// draw gear spokes
		ctx.beginPath();
		ctx.moveTo(w - a, h    );
		ctx.lineTo(w + a, h    );
		
		ctx.moveTo(w    , h - a);
		ctx.lineTo(w    , h + a);
		
		ctx.moveTo(w - b, h - b);
		ctx.lineTo(w + b, h + b);
		
		ctx.moveTo(w - b, h + b);
		ctx.lineTo(w + b, h - b);
		ctx.fill();
		ctx.stroke();
		
		// reset line width
		ctx.lineWidth = 1;
		
		// draw gear body
		ctx.beginPath();
		ctx.arc(w, h, 5, 0, 2 * Math.PI);
		ctx.fill();
		ctx.stroke();
		
		// gear hole fill style
		if (node.hover) {
			ctx.fillStyle = "#AAAAAA";
		} else {
			ctx.fillStyle = "#777777";
		}
		
		// draw gear hole
		ctx.beginPath();
		ctx.arc(w, h, 4, 0, 2 * Math.PI);
		ctx.fill();
		ctx.stroke();
		
		// reset fill style
		ctx.fillStyle = "#AAAAAA";
	}
	
	// draw settings menu
	if (settingsIndx >= 0) {
		// selected node and child
		var node  = nodes[settingsIndx];
		var child = -1;
		if (node.children.length > 0) {
			child = node.children[settingsChild];
		}
		
		// setting menu bounding box
		var l = cvs.width  / 2 - menuWidth ; // left side
		var t = cvs.height / 2 - menuHeight; // top side
		var r = cvs.width  / 2 + menuWidth ; // right side
		var b = cvs.height / 2 + menuHeight; // bottom side
		
		// draw menu rectangle
		ctx.beginPath();
		ctx.roundRect(l, t, 2 * menuWidth, 2 * menuHeight, 10);
		ctx.fill();
		ctx.stroke();
		
		// draw menu separation bars
		ctx.beginPath();
		ctx.moveTo(l + 30, t);
		ctx.lineTo(l + 30, b);
		ctx.moveTo(l + 30, t +  25);
		ctx.lineTo(r     , t +  25);
		ctx.moveTo(l + 30, t +  75);
		ctx.lineTo(r     , t +  75);
		ctx.moveTo(l + 30, t + 125);
		ctx.lineTo(r     , t + 125);
		ctx.moveTo(l + 30, t + 175);
		ctx.lineTo(r     , t + 175);
		ctx.moveTo(l + 30, t + 230);
		ctx.lineTo(r     , t + 230);
		ctx.fill();
		ctx.stroke();
		
		// close button fill style
		if (settingsClose) {
			ctx.fillStyle = "#FF7777";
		} else {
			ctx.fillStyle = "#FF0000";
		}
		
		// draw close button
		ctx.beginPath();
		ctx.roundRect(l + 5, t + 5, 20, 20, 2);
		ctx.fill();
		ctx.stroke();
		
		// close button decal style
		ctx.strokeStyle = "#FFFFFF";
		ctx.lineWidth   = 2;
		
		// draw close button decal
		ctx.beginPath();
		ctx.moveTo(l + 15 - 6, t + 15 - 6);
		ctx.lineTo(l + 15 + 6, t + 15 + 6);
		
		ctx.moveTo(l + 15 - 6, t + 15 + 6);
		ctx.lineTo(l + 15 + 6, t + 15 - 6);
		ctx.fill();
		ctx.stroke();
		
		// text style
		ctx.fillStyle   = "#000000";
		ctx.strokeStyle = "#000000";
		
		// text input cursors
		var nameCursor    = settingsMenu == 1 ? "|" : "";
		var formulaCursor = settingsMenu == 2 ? "|" : "";
		
		var nameText    = node.name.substring(0,settingsCursor);
		nameText += nameCursor + node.name.substring(settingsCursor);
		var formulaText = node.formula.substring(0,settingsCursor);
		formulaText += formulaCursor + node.formula.substring(settingsCursor);
		
		// draw settings menu text
		ctx.fillText("Delete Node " + node.id + "?", l + 55, t +  17);
		ctx.fillText("Name:",                        l + 55, t +  42);
		ctx.fillText(nameText,                       l + 55, t +  67);
		ctx.fillText("Formula:",                     l + 55, t +  92);
		ctx.fillText(formulaText,                    l + 55, t + 117);
		ctx.fillText("Inference Rule:",              l + 55, t + 142);
		ctx.fillText(infRules[node.infRule],         l + 55, t + 167);
		
		// show option to delete children if children exist
		if (child >= 0) {
			ctx.fillText("Delete Child " + child + "?",        l + 55, t + 192);
			ctx.fillText("{" + node.children.join(", ") + "}", l + 55, t + 221);
		}
		
		// error message text style
		ctx.fillStyle   = "#770000";
		
		// show error if error exists
		if (node.error != 0) {
			ctx.fillText(errMesgs[node.error], l + 55, t + 247);
		}
		
		// menu selectr arrow style
		ctx.fillStyle  = "#00FF00";
		ctx.font       = "bold 20px Arial";
		
		// menu selector arrow
		ctx.fillText("\u{2192}", l + 33, t + 20 + 50 * settingsMenu);
		
		// reset style
		ctx.lineWidth = 1;
		ctx.fillStyle = "#AAAAAA";
	}
}

// node updater
function update() {
	// loop over nodes
	for (var i = 0; i < nodes.length; i++) {
		var node = nodes[i];

		// reset values
		node.error = 0;
		node.latex = "";
		
		var isAtom = false; // is WFF atomic
		var isWFF  = false; // is WFF not atomic
		var isEnd  = false; // is end of WFF reached
		var count  = 0;     // parenthesis checksum
		
		// node formula string
		var str = node.formula;
		
		// loop through formula and count parenthesis
		for (var j = 0; j < str.length; j++) {
			s = str[j]; // current char
			if (s == " ") { // char is space
				if (isAtom) { // signify end of atom
					isEnd = true;
				} else { // else continue
					continue;
				}
			} else if (s == "(") { // char is open paren
				if (isEnd) { // formula is closed already
					node.error = 1; // invalid formula
					break;
				}
				if (!isAtom && !isWFF) { // check if WFF type is unassigned
					isWFF = true;
				} else if (isAtom) { // atom cannot have parens
					node.error = 1; // invalid formula
					break;
				}
				count += 1; // increase paren count
			} else if (s == ")") { // char is close paren
				// no need to check or set WFF type
				count -= 1; // decrease paren count
				if (count == 0) isEnd = true; // signify end of WFF
				if (count < 0) {
					node.error = 1; // invalid formula
					break;
				}
			} else if (!isAtom && !isWFF) { // check if WFF type is unassigned
				isAtom = true;
			} else if (isEnd) { // no non-space characters after end
				node.error = 1; // invalid formula
				break;
			}
		}
		
		// check if parenthesis checksum zeroes
		if (count != 0) node.error = 1; // invalid formula
		
		// check if error found in parsing formula
		if (node.error != 0) {
			node.latex = node.formula.trim();
			node.WFFTree = new WFFClass();
			continue;
		} else if (isAtom) { // check if parsed formula is atomic
			node.latex = node.formula.trim();
			node.WFFTree = new WFFClass();
			node.WFFTree.type = 1;
			node.WFFTree.name = node.latex;
			node.WFFTree.free = [node.latex];
			continue;
		} else if (!isWFF) { // empty formula
			node.WFFTree = new WFFClass();
			node.error = 2; // empty formula
			continue;
		}
		
		var stack     = ""; // identifier string stack
		var rootArray = []; // array of WFF tree roots
		var depth     = -1; // rootArray length - 1
		
		// loop over formula and build WFF
		for (var j = 0; j < str.length; j++) {
			var s = str[j]; // current char
			// check if char is special
			if (s == "(" || s == " " || s == ")") {
				if (stack.length > 0) { // check if identifier exists to push
					var newNode = new WFFClass();
					newNode.name = stack;
					newNode.type = 1;
					rootArray[depth].args.push(newNode); // push stack to current WFF
					stack = ""
				}
			} else { // else append char to stack
				stack += s;
			}
			if (s == "(") { // char is open parens
				if (rootArray.length > 0) { // check if WFF exists
					var newNode = new WFFClass();
					rootArray[depth].args.push(newNode); // push WFF to current WFF
					rootArray.push(newNode); // push new WFF to become current WFF
					depth += 1; // update depth
				} else { // create new WFF
					rootArray.push(new WFFClass());
					depth += 1; // update depth
				}
			}
			if (s == ")") { // char is close parens
				var root = rootArray[depth]; // WFF to be removed from rootArray
				if (root.args.length == 0) { // if parenthesis contain nothing
					node.error = 3; // missing identifier
				} else { // else take first argument as WFF name
					if (root.args[0].type != 1) { // check if first argument is not atomic
						node.error = 8; // invalid identifier
					}
					root.name = root.args[0].name;
					root.args.splice(0,1);
				}
				rootArray.pop(); // pop last WFF from rootArray
				depth -= 1; // update depth
				
				// check WFF type
				if (root.name == "and" && root.args.length >= 2) {
					// "and" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "or" && root.args.length >= 2) {
					// "or" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "if" && root.args.length == 2) {
					// "if" with exactly 2 inputs
					root.type = 4;
				} else if (root.name == "iff" && root.args.length == 2) {
					// "iff" with exactly 2 inputs
					root.type = 4;
				} else if (root.name == "=" && root.args.length >= 2) {
					// "=" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "+" && root.args.length >= 2) {
					// "+" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "-" && root.args.length >= 2) {
					// "-" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "*" && root.args.length >= 2) {
					// "*" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "times" && root.args.length >= 2) {
					// "times" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "ast" && root.args.length >= 2) {
					// "ast" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "star" && root.args.length >= 2) {
					// "star" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "~" && root.args.length >= 2) {
					// "~" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "sim" && root.args.length >= 2) {
					// "sim" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "cong" && root.args.length >= 2) {
					// "cong" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "equiv" && root.args.length >= 2) {
					// "equiv" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "oplus" && root.args.length >= 2) {
					// "oplus" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "otimes" && root.args.length >= 2) {
					// "otimes" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "|" && root.args.length >= 2) {
					// "|" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "div" && root.args.length >= 2) {
					// "div" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "<" && root.args.length >= 2) {
					// "div" with at least 2 inputs
					root.type = 4;
				} else if (root.name == ">" && root.args.length >= 2) {
					// "div" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "le" && root.args.length >= 2) {
					// "div" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "ge" && root.args.length >= 2) {
					// "div" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "in" && root.args.length >= 2) {
					// "in" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "cup" && root.args.length >= 2) {
					// "cup" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "cap" && root.args.length >= 2) {
					// "cap" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "subset" && root.args.length >= 2) {
					// "subset" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "subseteq" && root.args.length >= 2) {
					// "subseteq" with at least 2 inputs
					root.type = 4;
				} else if (root.name == "not" && root.args.length == 1) {
					// "not" with exactly 1 input
					root.type = 3;
				} else if (root.name == "-" && root.args.length == 1) {
					// "not" with exactly 1 input
					root.type = 3;
				} else if (root.name == "!" && root.args.length == 1) {
					// "not" with exactly 1 input
					root.type = 3;
				} else if ((root.name == "exists" || root.name == "forall") && root.args.length >= 2) {
					// "exists" or "forall" with at least 2 inputs
					root.type = 5;
					// check if all but last inputs are atomic
					for (var k = 0; k < root.args.length - 1; k++) {
						if (root.args[k].type > 1) { // if input is not atomic or special
							root.type = 2; // set as unmatched
						}
					}
				} else if (root.args.length == 0) {
					// any with exactly 0 inputs
					root.type = 0;
				} else {
					// unmatched
					root.type = 2;
				}
			}
		}
		
		// determine variable bind type in WFF
		root.bindVars();
		
		// check if WFF has repeated bound variables
		if ((new Set(root.bndb)).size !== root.bndb.length) {
			node.error = 5; // variable is already bound
		}
		
		// check if WFF has a variable that is both free and bound
		if (root.bndb.filter(function(e) {return root.free.indexOf(e) > -1;}).length > 0) {
			node.error = 6; // variable cannot be both bound and free
		}
		
		// assign node values
		node.latex   = root.print();
		node.WFFTree = root;
		
		// check if node has no error nor set inference rule
		if ((node.error == 0) && (node.infRule == 0)) {
			node.error = 7; // no selected inference rule
		}
	}
	
	// recheck logic
	recheck();
	
	// loop through nodes
	for (var i = 0; i < nodes.length; i++) {
		var node = nodes[i];
		
		// set font style for measurment
		ctx.font = "16px Arial";
		
		// set node width
		node.width = Math.max(100,
							  35 + ctx.measureText("{" + node.scope.join(", ") + "}").width,
							  10 + ctx.measureText(node.name).width,
							  10 + ctx.measureText(node.latex).width,
							  10 + ctx.measureText(infRules[node.infRule]).width) / 2;
	}
	
	// redraw scene
	draw();
}

// logic recheker
function recheck() {
	// topological sorting
	var nodesCopy     = []; // reduced copy of nodes keeping connections
	var startingNodes = []; // nodes with no inputs
	var topSortTable  = []; // topological sort ID table
	
	// fill nodesCopy
	for (var i = 0; i < nodes.length; i++) {
		var node = new nodeClass(); // reduced copy to be filled
		node.id = i; // node ID
		
		// populate children
		for (var j = 0; j < nodes[nodesIdTable[i]].children.length; j++) {
			node.children.push(nodes[nodesIdTable[i]].children[j]);
		}
		
		// populate parents
		for (var j = 0; j < nodes[nodesIdTable[i]].parents.length; j++) {
			node.parents.push(nodes[nodesIdTable[i]].parents[j]);
		}
		
		// push node ID if no parents
		if (node.parents.length == 0) startingNodes.push(i);
		
		// push new node
		nodesCopy.push(node);
	}
	
	// Kahn's algorithm
	while (startingNodes.length > 0) {
		// remove first node from startingNodes
		var node = nodesCopy[startingNodes[0]];
		startingNodes.splice(0,1);
		
		// push position of node
		topSortTable.push(nodesIdTable[node.id]);
		
		// loop over children of node and remove itself as parent
		for (var i = 0; i < node.children.length; i++) {
			// node child
			var child = nodesCopy[node.children[i]];
			
			// remove node as parent of child
			child.parents.splice(child.parents.indexOf(node.id), 1);
			
			// check if child has no parents
			// add to startingNodes if so
			if (child.parents.length == 0) startingNodes.push(child.id);
		}
	}
	
	// nodesCopy contains nodes with parents if and only if there are cycles
	// loop over nodes and check for parents and mark circular logic error if so
	for (var i = 0; i < nodesCopy.length; i++) {
		if (nodesCopy[i].parents.length > 0) {
			nodes[nodesIdTable[nodesCopy[i].id]].error = 4; // circular logic
		}
	}
	
	// loop over nodes amd reset dependencies and validity
	for (var i = 0; i < nodes.length; i++) {
		nodes[i].valid  = false;
		nodes[i].scope = [];
	}
	
	// loop over nodes not in cycles
	for (var i = 0; i < topSortTable.length; i++) {
		var node = nodes[topSortTable[i]];
		
		// loop over parents and inherit dependencies
		for (var j = 0; j < node.parents.length; j++) {
			var parent = nodes[nodesIdTable[node.parents[j]]];
			// loop over parent dependencies
			for (var k = 0; k < parent.scope.length; k++) {
				node.scope.push(parent.scope[k]);
			}
		}
		
		// check if node has no error
		if (node.error == 0) {
			// pass node into inference rule function
			infRulesFuncs[node.infRule](node);
		} 
		
		// check if inference rule failed to hold
		if (node.error != 0) {
			// push error node itself as dependency
			node.scope.push(node.id);
		}
		
		// sort and remove duplicate dependencies
		node.scope = [...new Set(node.scope)];
		node.scope.sort();
	}
}

// inference rule checker functions

// assume
function funcAssume(node) {
	// check if node has inputs
	if (node.parents.length > 0) {
		node.error = 12; // assumptions cannot have inputs
		return;
	}
	
	// else node is valid
	node.valid = true;
	
	// assumption in own scope
	node.scope.push(node.id);
}

// and intro
function funcAndIntro(node) {
	var WFF = node.WFFTree;
	
	if (WFF.atomic) { // check if formula is atomic
		node.error = 13; // conjunction is not introduced
		return;
	} else if (WFF.name != 'and') { // check if WFF name is not 'and'
		node.error = 13; // conjunction is not introduced
		return;
	} else if (WFF.type != 4) {
		node.error = 9; // too few arguments
		return;
	}
	
	// WFF value marker array
	var marker = Array(WFF.args.length).fill(0);
	
	// loop over parents
	for (var i = 0; i < node.parents.length; i++) {
		var pWFF = nodes[nodesIdTable[node.parents[i]]].WFFTree;
		var found = false; // is argument in node WFF matched?
		// loop over node WFF arguments
		for (var j = 0; j < WFF.args.length; j++) {
			if (marker[j] == 1) continue; // skip over marked arguments
			if (WFF.args[j].equals(pWFF)) { // check if arguments match
				marker[j] = 1; // mark
				found = true;
				break;
			}
		}
		// has parent WFF been unmatched?
		if (!found) {
			node.error = 11; // unmatched input propositions
			return;
		}
	}
	
	// loop over unmarked WFF arguments
	for (var j = 0; j < WFF.args.length; j++) {
		if (marker[j] == 1) continue; // skip over marked arguments
		// loop over parents
		for (var i = 0; i < node.parents.length; i++) {
			var pWFF = nodes[nodesIdTable[node.parents[i]]].WFFTree;
			if (WFF.args[j].equals(pWFF)) { // check if unmarked argument is matched
				marker[j] = 1;
			}
		}
		// check if argument remains unmarked
		if (marker[j] == 0) {
			node.error = 10; // missing input propositions
			return;
		}
	}
	
	// inference is valid
	node.valid = true;
}

// and elim
function funcAndElim(node) {
	var WFF = node.WFFTree;
	
	if (node.parents.length > 1) { // check if too many inputs
		node.error = 11; // unmatched input propositions
		return;
	} else if (node.parents.length == 0) { // check if no inputs
		node.error = 10; // missing input propositions
		return;
	}
	
	// parent WFF
	var pWFF = nodes[nodesIdTable[node.parents[0]]].WFFTree;
	
	if (pWFF.name != 'and') { // check if single parent is 'and'
		node.error = 14; // conjunction is not eliminated
		return;
	} else if (pWFF.type != 4) { // 'and' is of wrong arity
		node.error = 14; // conjunction is not eliminated
		return;
	}
	
	// loop over parent arguments
	for (var i = 0; i < pWFF.args.length; i++) {
		if (WFF.equals(pWFF.args[i])) {
			node.valid = true;
			return;
		}
	}
	
	node.error = 15; // proposition not found in conjunction
}

// or intro
function funcOrIntro(node) {
	var WFF = node.WFFTree;
	
	if (WFF.atomic) { // check if formula is atomic
		node.error = 16; // disjunction is not introduced
		return;
	} else if (WFF.name != 'or') {
		node.error = 16; // disjunction is not introduced
		return;
	} else if (WFF.type != 4) { // 'or' is of wrong arity
		node.error = 9; // too few arguments
		return;
	}
	
	if (node.parents.length > 1) { // check if too many inputs
		node.error = 11; // unmatched input propositions
		return;
	} else if (node.parents.length == 0) { // check if no inputs
		node.error = 10; // missing input propositions
		return;
	}
	
	// parent WFF
	var pWFF = nodes[nodesIdTable[node.parents[0]]].WFFTree;
	
	
	// loop over parent arguments
	for (var i = 0; i < WFF.args.length; i++) {
		if (pWFF.equals(WFF.args[i])) { // check if one argument equals proposition
			node.valid = true;
			return;
		}
	}
	
	node.error = 17; // proposition not found in disjunction
}

// or elim
function funcOrElim(node) {
	var WFF  = node.WFFTree;
	var mark = -1;
	
	// check if node has inputs.
	if (node.parents.length == 0) {
		node.error = 10; // missing input propositions
		return;
	}
	
	for (var i = 0; i < node.parents.length; i++) {
		var pWFF = nodes[nodesIdTable[node.parents[i]]].WFFTree;
		
		if (pWFF.equals(WFF)) { // parent node is equal to node propositoin
			continue;
		}
		
		// check if parent node is a valid and new 'or'
		if ((mark == -1) && (pWFF.name == "or") && (pWFF.type == 4)) {
			mark = i;
		} else { // extra input node found
			node.error = 11; // unmatched input propositions
			return;
		}
	}
	
	if (mark != -1) { // check if mark exists
		// run helper function using mark as cases
		helpOrElim(node, mark)
	} else { // else try each input as cases
		// no disjunction to eliminate
		if ((WFF.name != "or") || (WFF.type != 4)) {
			node.error = 18; // disjunction is not eliminated
			return;
		}
		
		// loop over inputs and try each as the cases node
		for (var i = 0; i < node.parents.length; i++) {
			node.error = 0; // reset node error
			helpOrElim(node, i);
			
			// success has been found
			if (node.error == 0) {
				break;
			}
		}
	}
	
	// success found
	if (node.error == 0) {
		node.valid = true;
	}
}

// or elim helper
function helpOrElim(node, mark) {
	// mark node
	var mNode = nodes[nodesIdTable[node.parents[mark]]];
	
	var  WFF = node.WFFTree;  // node WFF
	var mWFF = mNode.WFFTree; // mark node WFF
	
	var found   = false; // has proposition been derived from case?
	var inScope = false; // is proposition in scope of particular parent?
	
	// reset node scope
	var scopeTemp = node.scope;
	node.scope = [];
	
	// loop over mark node arguments
	for (var i = 0; i < mWFF.args.length; i++) {
		var aWFF = mWFF.args[i];
		found = false; // reset found variable
		
		// loop over parent nodes
		for (var j = 0; j < node.parents.length; j++) {
			if (j == mark) {
				// loop over mark node scope
				var sNode = nodes[nodesIdTable[node.parents[j]]];
				for (var k = 0; k < sNode.scope.length; k++) {
					node.scope.push(sNode.scope[k]);
				}
				// skip to next node
				continue;
			}
			
			// reset inScope
			inScope = false;
			
			// parent node
			var pNode = nodes[nodesIdTable[node.parents[j]]];
			
			// loop over parent node scope nodes
			// check if parent is derived from case
			for (var k = 0; k < pNode.scope.length; k++) {
				var sWFF = nodes[nodesIdTable[pNode.scope[k]]].WFFTree;
				
				if (sWFF.equals(aWFF)) {
					found   = true;
					inScope = true;
				}
			}
			
			// skip if proposition not in parent node scope
			if (!inScope) continue;
			
			// reset inScope
			inScope = false;
			
			// loop over parent node scope nodes
			// push dependencies
			for (var k = 0; k < pNode.scope.length; k++) {
				var sWFF = nodes[nodesIdTable[pNode.scope[k]]].WFFTree;
				
				if (sWFF.equals(aWFF) && !inScope) {
					inScope = true;
				} else {
					node.scope.push(pNode.scope[k]);
				}
			}
		}
		
		// no match has been found
		if (!found) {
			node.error = 19; // proposition not derived from case
			node.scope = scopeTemp;
		}
	}
	
	// sort and remove duplicate dependencies
	node.scope = [...new Set(node.scope)];
	node.scope.sort();
}

// not intro
function funcNotIntro(node) {
	var WFF = node.WFFTree;
	
	// check if proposition is a negation
	if ((WFF.name != "not") || (WFF.type != 3)) {
		node.error = 20; // negation is not introduced
		return;
	}
	
	if (node.parents.length > 2) { // check if too many inputs
		node.error = 11; // unmatched input propositions
		return;
	} else if (node.parents.length < 2) { // check if no inputs
		node.error = 10; // missing input propositions
		return;
	}
	
	// parent nodes
	var pNode0 = nodes[nodesIdTable[node.parents[0]]];
	var pNode1 = nodes[nodesIdTable[node.parents[1]]];
	
	// parent WFFs
	var pWFF0 = pNode0.WFFTree;
	var pWFF1 = pNode1.WFFTree;
	
	// check if first parent is a negation
	if ((pWFF0.name == "not") && (pWFF0.type == 3)) {
		// check if first parent is a negation of the second parent
		if (pWFF0.args[0].equals(pWFF1)) {
			node.valid = true;
		}
	}
	
	// check if second parent is a negation
	if ((pWFF1.name == "not") && (pWFF1.type == 3)) {
		// check if second parent is a negation of the first parent
		if (pWFF1.args[0].equals(pWFF0)) {
			node.valid = true;
		}
	}
	
	// either case failed
	if (!node.valid) {
		node.error = 21; // input propositions are not a contradiction
		return;
	}
	
	// reset node validity and scope
	node.valid = false;
	node.scope = [];
	
	// scope has been discharged
	var found = false;
	
	// loop over first parent scope
	for (var i = 0; i < pNode0.scope.length; i++) {
		var sNode = nodes[nodesIdTable[pNode0.scope[i]]];
		// check if node WFF is negation of scope node
		// first instance of match gets discharged
		if ((sNode.WFFTree.equals(WFF.args[0])) && !found) {
			node.valid = true;
			found = true;
		} else { // push scope
			node.scope.push(pNode0.scope[i]);
		}
	}
	
	// reset found to discharge additional scopes
	found = false;
	
	// loop over second parent scope
	for (var i = 0; i < pNode1.scope.length; i++) {
		var sNode = nodes[nodesIdTable[pNode1.scope[i]]];
		// check if node WFF is negation of scope node
		// first instance of match gets discharged
		if ((sNode.WFFTree.equals(WFF.args[0])) && !found) {
			node.valid = true;
			found = true;
		} else { // push scope
			node.scope.push(pNode1.scope[i]);
		}
	}
	
	// no match for negation found
	if (!node.valid) {
		node.error = 22; // negation of proposition missing in scope of inputs
	}
}

// not elim
function funcNotElim(node) {
var WFF = node.WFFTree;
	
	if (node.parents.length > 2) { // check if too many inputs
		node.error = 11; // unmatched input propositions
		return;
	} else if (node.parents.length < 2) { // check if no inputs
		node.error = 10; // missing input propositions
		return;
	}
	
	// parent nodes
	var pNode0 = nodes[nodesIdTable[node.parents[0]]];
	var pNode1 = nodes[nodesIdTable[node.parents[1]]];
	
	// parent WFFs
	var pWFF0 = pNode0.WFFTree;
	var pWFF1 = pNode1.WFFTree;
	
	// check if first parent is a negation
	if ((pWFF0.name == "not") && (pWFF0.type == 3)) {
		// check if first parent is a negation of the second parent
		if (pWFF0.args[0].equals(pWFF1)) {
			node.valid = true;
		}
	}
	
	// check if second parent is a negation
	if ((pWFF1.name == "not") && (pWFF1.type == 3)) {
		// check if second parent is a negation of the first parent
		if (pWFF1.args[0].equals(pWFF0)) {
			node.valid = true;
		}
	}
	
	// either case failed
	if (!node.valid) {
		node.error = 21; // input propositions are not a contradiction
		return;
	}
	
	// reset node validity and scope
	node.valid = false;
	node.scope = [];
	
	// scope has been discharged
	var found = false;
	
	// loop over first parent scope
	for (var i = 0; i < pNode0.scope.length; i++) {
		var sWFF = nodes[nodesIdTable[pNode0.scope[i]]].WFFTree;
		var cond1 = sWFF.name == "not"; // scope WFF is negation
		var cond2 = sWFF.type == 3;     // scope WFF is binary
		// short circuit when conditions 1 and 2 fail
		if (!found && cond1 && cond2 && sWFF.args[0].equals(WFF)) {
			node.valid = true;
			found = true;
		} else { // push scope when no match or when match has already been found
			node.scope.push(pNode0.scope[i]);
		}
	}
	
	// reset found to discharge additional scopes
	found = false;
	
	for (var i = 0; i < pNode1.scope.length; i++) {
		var sWFF = nodes[nodesIdTable[pNode1.scope[i]]].WFFTree;
		var cond1 = sWFF.name == "not"; // scope WFF is negation
		var cond2 = sWFF.type == 3;     // scope WFF is binary
		// short circuit when conditions 1 and 2 fail
		if (!found && cond1 && cond2 && sWFF.args[0].equals(WFF)) {
			node.valid = true;
			found = true;
		} else { // push scope when no match or when match has already been found
			node.scope.push(pNode1.scope[i]);
		}
	}
	
	// no match for negation found
	if (!node.valid) {
		node.error = 23; // negation is not eliminated
	}
}

// if intro
function funcIfIntro(node) {
	var WFF = node.WFFTree;
	
	// check if proposition is conditional
	if ((WFF.name != 'if') || (WFF.type != 4)) {
		node.error = 24; // conditional is not introduced
		return;
	}
	
	if (node.parents.length > 1) { // check if too many inputs
		node.error = 11; // unmatched input propositions
		return;
	} else if (node.parents.length < 1) { // check if no inputs
		node.error = 10; // missing input propositions
		return;
	}
	
	// parent WFF
	var pNode = nodes[nodesIdTable[node.parents[0]]];
	
	// check if parent is not consequent of conditional
	if (!WFF.args[1].equals(pNode.WFFTree)) {
		node.error = 25; // input is not consequent of conditional 
		return;
	}
	
	// reset node scope
	node.scope = [];
	
	// loop over parent scope
	for (var i = 0; i < pNode.scope.length; i++) {
		var sNode = nodes[nodesIdTable[pNode.scope[i]]];
		// check if scope matches precedent and no prior match has been made
		if ((sNode.WFFTree.equals(WFF.args[0])) && !node.valid) {
			node.valid = true;
		} else { // else push scope
			node.scope.push(pNode.scope[i]);
		}
	}
	
	// no match has been made
	if (!node.valid) {
		node.error = 26; // antecedent of conditional is not in scope of input
	}
}

// if elim
function funcIfElim(node) {
	var WFF = node.WFFTree;
	
	if (node.parents.length > 2) { // check if too many inputs
		node.error = 11; // unmatched input propositions
		return;
	} else if (node.parents.length < 2) { // check if no inputs
		node.error = 10; // missing input propositions
		return;
	}
	
	// parent WFFs
	var pWFF0 = nodes[nodesIdTable[node.parents[0]]].WFFTree;
	var pWFF1 = nodes[nodesIdTable[node.parents[1]]].WFFTree;
	
	// check if first parent is a conditional
	if ((pWFF0.name == 'if') && (pWFF0.type == 4)) {
		// check if second parent is precedent of first parent
		if (pWFF0.args[0].equals(pWFF1)) {
			// check if node WFF is consequent of first parent
			if (pWFF0.args[1].equals(WFF)) {
				node.valid = true;
				return;
			} else {
				node.error = 27; // proposition is not consequent of conditional
				return;
			}
		} else {
			node.error = 28; // input is not antecedent of conditional
			return;
		}
		// check if second parent is a conditional
	} else if ((pWFF1.name == 'if') && (pWFF1.type == 4)) {
		// check if first parent is precedent of second parent
		if (pWFF1.args[0].equals(pWFF0)) {
			// check if node WFF is consequent of second parent
			if (pWFF1.args[1].equals(WFF)) {
				node.valid = true;
				return;
			} else {
				node.error = 27; // proposition is not consequent of conditional
				return;
			}
		} else {
			node.error = 28; // input is not antecedent of conditional
			return;
		}
	}
	
	node.error = 29; // conditional is not eliminated
}

// iff intro
function funcIffIntro(node) {
	var WFF = node.WFFTree;
	
	// check if node is not a biconditional
	if ((WFF.name != "iff") || (WFF.type != 4)) {
		node.error = 30; // biconditional is not introduced
		return;
	}
	
	if (node.parents.length > 2) { // check if too many inputs
		node.error = 11; // unmatched input propositions
		return;
	} else if (node.parents.length < 2) { // check if no inputs
		node.error = 10; // missing input propositions
		return;
	}
	
	// parent WFFs
	var pWFF0 = nodes[nodesIdTable[node.parents[0]]].WFFTree;
	var pWFF1 = nodes[nodesIdTable[node.parents[1]]].WFFTree;
	
	// check if first parent is not a conditional
	if ((pWFF0.name != "if") || (pWFF0.type != 4)) {
		node.error = 11; // unmatched input propositions
		return;
	}
	
	// check if second parent is not a conditional
	if ((pWFF1.name != "if") || (pWFF1.type != 4)) {
		node.error = 11; // unmatched input propositions
		return;
	}
	
	// check if biconditional matches any entries in each conditional
	var a1 = pWFF0.args[0].equals(WFF.args[0]);
	var b1 = pWFF0.args[1].equals(WFF.args[1]);
	var c1 = pWFF1.args[0].equals(WFF.args[1]);
	var d1 = pWFF1.args[1].equals(WFF.args[0]);
	var a2 = pWFF0.args[0].equals(WFF.args[1]);
	var b2 = pWFF0.args[1].equals(WFF.args[0]);
	var c2 = pWFF1.args[0].equals(WFF.args[0]);
	var d2 = pWFF1.args[1].equals(WFF.args[1]);
	
	// check if first conditional matches biconditional and second conditional is reversed
	// or the same with the first and second conditionals swapped
	if ((a1 && b1 && c1 && d1) || (a2 && b2 && c2 && d2)) {
		node.valid = true;
	} else {
		node.error = 11; // unmatched input propositions
	}
}

// iff elim
function funcIffElim(node) {
	var WFF = node.WFFTree;
	
	if (node.parents.length > 1) { // check if too many inputs
		node.error = 11; // unmatched input propositions
		return;
	} else if (node.parents.length < 1) { // check if no inputs
		node.error = 10; // missing input propositions
		return;
	}
	
	// parent WFF
	var pWFF = nodes[nodesIdTable[node.parents[0]]].WFFTree;
	
	// check if parent WFF is not a biconditional
	if ((pWFF.name != "iff") || (pWFF.type != 4)) {
		node.error = 31; // biconditional is not eliminated
		return;
	}
	
	// cheeck if node WFF is not a conditional
	if ((WFF.name != "if") || (WFF.type != 4)) {
		node.error = 24; // conditional is not introduced
		return;
	}
	
	// check if conditional matches biconditional
	var a1 = pWFF.args[0].equals(WFF.args[0]);
	var b1 = pWFF.args[1].equals(WFF.args[1]);
	var a2 = pWFF.args[0].equals(WFF.args[1]);
	var b2 = pWFF.args[1].equals(WFF.args[0]);
	
	// check if conditional matches biconditional or reversed biconditional
	if ((a1 && b1) || (a2 && b2)) {
		node.valid = true;
	} else {
		node.error = 11; // unmatched input propositions
	}
}

// equals intro
function funcEqualsIntro(node) {
	// check if node has inputs
	if (node.parents.length > 0) {
		node.error = 32; // equality introduction cannot have inputs
		return;
	}
	
	var WFF = node.WFFTree;
	
	if (WFF.atomic) { // check if formula is atomic
		node.error = 33; // equality is not introduced
		return;
	} else if (WFF.name != '=') { // check if WFF name is not '='
		node.error = 33; // conjunction is not introduced
		return;
	} else if (WFF.type != 4) {
		node.error = 9; // too few arguments
		return;
	}
	
	// loop over WFF arguments
	for (var i = 1; i < WFF.args.length; i++) {
		// check if term is not equal to first term
		if (!WFF.args[0].equals(WFF.args[i])) {
			node.error = 34; // propositions are not equal
			return;
		}
	}
	
	// inference is valid
	node.valid = true;
}

// equals elim
function funcEqualsElim(node) {
	var WFF = node.WFFTree;
	
	if (node.parents.length > 2) { // check if too many inputs
		node.error = 11; // unmatched input propositions
		return;
	} else if (node.parents.length < 1) { // check if no inputs
		node.error = 10; // missing input propositions
		return;
	}
	
	// parents 1 WFF
	var pWFF0 = nodes[nodesIdTable[node.parents[0]]].WFFTree;
	
	if (node.parents.length == 1) {
		if (pWFF0.name == "=") {
			if (WFF.equalsElim(pWFF0, pWFF0)) {
				node.valid = true;
				return;
			}
		}
		
		node.error = 10; // missing input propositions
		return;
	}
	
	// parent 2 WFF
	var pWFF1 = nodes[nodesIdTable[node.parents[1]]].WFFTree;
	
	if ((pWFF0.name != "=") && (pWFF1.name != "=")) {
		node.error = 35; // equality is not eliminated
		return;
	}
	
	var temp = false; // true if equality subsitues free and bound variables
	
	// check if first parent is equality
	if (pWFF0.name == "=") {
		if (WFF.equalsElim(pWFF1, pWFF0)) {
			node.valid = true;
		}
		
		// loop over equal terms
		for (var i = 0; i < pWFF0.args.length; i++) {
			// check if term in equality is a bound variable
			if (pWFF1.bndb.includes(pWFF0.args[i].name)) temp = true;
		}
	}
	
	// check if second parent is equality
	if (pWFF1.name == "=") {
		if (WFF.equalsElim(pWFF0, pWFF1)) {
			node.valid = true;
			temp = false; // reset marker
		}
		
		// loop over equal terms
		for (var i = 0; i < pWFF1.args.length; i++) {
			// check if term in equality is a bound variable
			if (pWFF0.bndb.includes(pWFF1.args[i].name)) temp = true;
		}
	}
	
	if (node.valid) {
		if (temp) {
			node.error = 36; // cannot equate bound variables
			node.valid = false;
		}
	} else {
		node.error = 34; // propositions are not equal
	}
}

// forall intro
function funcForallIntro(node) {
	var WFF = node.WFFTree;
	
	// check if proposition is universal quantifier
	if ((WFF.name != 'forall') || (WFF.type != 5)) {
		node.error = 37; // universal quantifier is not introduced
		return;
	}
	
	if (node.parents.length > 1) { // check if too many inputs
		node.error = 11; // unmatched input propositions
		return;
	} else if (node.parents.length < 1) { // check if no inputs
		node.error = 10; // missing input propositions
		return;
	}
	
	// bound variables
	var bVar = [];
	
	// loop over WFF args and push bound variable names to bVar
	for (var i = 0; i < WFF.args.length - 1; i++) {
		bVar.push(WFF.args[i].name);
	}
	
	// quantified WFF
	var qWFF = WFF.args[WFF.args.length - 1];
	
	// parent node
	var pNode = nodes[nodesIdTable[node.parents[0]]];
	
	// parent WFF
	var pWFF = pNode.WFFTree;
	
	// loop over bound variables of proposition
	for (var i = 0; i < WFF.args.length - 1; i++) {
		// check if bound variable is free in parent
		if (pWFF.free.includes(WFF.args[i].name)) {
			node.error = 38; // bound variable is present in input
			return;
		}
		// check if bound variable is bound in parent
		if (pWFF.bndb.includes(WFF.args[i].name)) {
			node.error = 38; // bound variable is present in input
			return;
		}
	}
	
	// variable substitution pairs
	var pairs = [];
	
	// populate pairs and determine if WFFs are equal up to variable substitution
	var pass = qWFF.forallIntro(pWFF, pairs);
	
	// check if WFFs are equal up to variable substitution
	if (!pass) {
		node.error = 39; // proposition is not generalization of input
		return;
	}
	
	// remove duplicate pairs
	var temp1 = []; // unique pairs
	var temp2 = []; // pair fingerprints
	
	// loop over pairs
	for (var i = 0; i < pairs.length; i++) {
		if (!temp2.includes(pairs[i][0] + " " + pairs[i][1])) {
			temp2.push(pairs[i][0] + " " + pairs[i][1]);
			temp1.push(pairs[i]);
		}
	}
	
	// replace pairs
	pairs = temp1;
	
	// seen substituted variables in parent
	var sVar = [];
	
	// loop over pairs
	for (var i = 0; i < pairs.length; i++) {
		// check if first term of pair is not bound variable of WFF
		if (!bVar.includes(pairs[i][0])) {
			node.error = 39; // proposition is not generalization of input
			return;
		}
		
		// check if second term has been seen before
		// arbitrary variable can only be generalized to a single bound variable
		if (!sVar.includes(pairs[i][1])) {
			sVar.push(pairs[i][1]);
		} else {
			node.error = 40; // arbitrary variable generalized to multiple bound variables
			return;
		}
		
		// check if free variable is free in proposition
		if (WFF.free.includes(pairs[i][1])) {
			node.error = 41; // arbitrary variable of input is present in proposition
			return;
		}
		// check if free variable is bound in proposition
		if (WFF.bndb.includes(pairs[i][1])) {
			node.error = 41; // arbitrary variable of input is present in proposition
			return;
		}
	}
	
	// loop over scope of parent
	for (var i = 0; i < pNode.scope.length; i++) {
		var sWFF = nodes[nodesIdTable[pNode.scope[i]]].WFFTree;
		
		// loop over bound variables
		for (var j = 0; j < sVar.length; j++) {
			if (sWFF.free.includes(sVar[i])) {
				node.error = 42; // arbitrary variable of input is free in scope of input
				return;
			}
		}
	}
	
	// inference is valid
	node.valid = true;
}

// forall elim
function funcForallElim(node) {
	var WFF = node.WFFTree;
	
	if (node.parents.length > 1) { // check if too many inputs
		node.error = 11; // unmatched input propositions
		return;
	} else if (node.parents.length < 1) { // check if no inputs
		node.error = 10; // missing input propositions
		return;
	}
	
	// parent WFF
	var pWFF = nodes[nodesIdTable[node.parents[0]]].WFFTree;
	
	// check if parent WFF is not a universal quantifier
	if ((pWFF.name != "forall") || (pWFF.type != 5)) {
		node.error = 43; // universal quantifier is not eliminated
		return;
	}
	
	// parent error ID
	var pErr = nodes[nodesIdTable[node.parents[0]]].error;
	
	// check if parent WFF is a valid quantifier
	if ((pErr == 5) || (pErr == 6)) {
		node.error = 44; // input proposition has invalid quantifer form
		return;
	}
	
	// parent quantified WFF
	var pqWFF = pWFF.args[pWFF.args.length - 1];
	
	// test bounding variables being set
	// k = 0 : test for all bound variables being set
	// k = 1 : test for some bound variables being set
	for (var k = 0; k < 2; k++) {
		// bound variable substitution pairs
		var pairs = [];
		
		if (k == 0) {
			// populate pairs
			for (var i = 0; i < pWFF.args.length - 1; i++) {
				pairs.push([pWFF.args[i].name, -1]);
			}
			
			// determine substitution pairs and substitution validity
			node.error = WFF.forallElim(pqWFF, pairs);
			
			// check if WFF is universal quantifier
		} else if ((WFF.name == "forall") && (WFF.type == 5)){
			var index = 0; // WFF bound variable cursor
			
			// loop over parent WFF bound variables
			for (var i = 0; i < pWFF.args.length - 1; i++) {
				// check if index is in range and corresponding bound variables match
				if ((index < WFF.args.length) && (pWFF.args[i].name == WFF.args[index].name)) {
					index += 1; // increment index
				} else {
					// push substituted variable
					pairs.push([pWFF.args[i].name,-1]);
				}
			}
			
			// check if all WFF bound variables are accounted for
			if (index < WFF.args.length - 1) {
				node.error = 49; // unnasigned bound variables
				return;
			}
			
			// check if substitution can be made
			if (pairs.length == 0) {
				node.error = 43; // universal quantifier is not eliminated
				return;
			}
			
			// determine substitution pairs and substitution validity
			node.error = WFF.args[WFF.args.length - 1].forallElim(pqWFF, pairs);
		} else { // skip second pass otherwise
			return;
		}
		
		// check if all variables have been assigned
		var check = true;
	
		// check if substitution raised no errors
		if (node.error == 0) {
			// check if free variables of WFF differ from bound variables of parent WFF
			// loop over WFF free variables
			for (var i = 0; i < WFF.free.length; i++) {
				if (pWFF.bndb.includes(WFF.free[i])) {
					node.error = 46; // bound variable of input is free in proposition
				}
			}
			
			// only run when node is still error free
			if (node.error == 0) {
				// loop over pairs
				for (var i = 0; i < pairs.length; i++) {
					// check if variable remains unassigned
					if (pairs[i][1] == -1) {
						// check if bound variable is present in parent WFF
						if (pqWFF.contains(pairs[i][0])) {
							check = false;
							node.error = 47; // bound variable is not assigned
							break;
						}
					} else { // check if assignment contains bound variable
						// loop over WFF bound variables
						for (var j = 0; j < WFF.bndb.length; j++) {
							// unbind parent WFF
							pWFF.unbindVars();
							
							// bind parent quantified WFF
							pqWFF.bindVars();
							
							// check if assignment contains variable bound in parent quntified WFF
							if (pairs[i][1].contains(pqWFF.bndb[j])) {
								check = false;
								node.error = 48; // cannot substitute bound variables
								
								// reset bindings
								pqWFF.unbindVars();
								pWFF.bindVars();
								
								break;
							}
							// reset bindings
							pqWFF.unbindVars();
							pWFF.bindVars();
						}
					}
				}
				
				// check if inference rule is successful
				if (check) {
					node.valid = true;
					return;
				}
			}
		}
	}
}		


// exists intro
function funcExistsIntro(node) {}

// exists elim
function funcExistsElim(node) {}

draw();
