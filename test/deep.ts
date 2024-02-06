function main() {
    exists(1)
}

function exists(a: number): boolean {
    function inner() {
	function even_innerer() {

	}
	even_innerer()
    }
    inner()
}
