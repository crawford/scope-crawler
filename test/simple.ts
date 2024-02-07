interface Shape {
    area(): number
}

class Square implements Shape {
    area(): number {
	1
    }
}

function main() {
    (new Square() as Shape).area()
    // new Square().area()
}
