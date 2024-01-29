function add(a, b) {
    return a + b;
}

function multiply(x, y) {
    return x * y;
}

class Test {
    do_thing(a, b) {
	function inner() {
	    add(a,b)
	}
	inner()
    }
}

let result1 = add(1, 2);
let result2 = multiply(3, 4);
let result3 = add(result1, result2);
let result4 = Test().do_thing(5,6);
