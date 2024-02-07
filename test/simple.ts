interface Shape<T> {
    area(): T
}

class Square implements Shape<number> {
    area(): number {
	    return 1
    }
}

function main() {
    (new Square() as Shape<number>).area()
    // new Square().area()
}
