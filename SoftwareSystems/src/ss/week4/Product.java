package ss.week4;

public class Product implements Function {
	private Function f;
	private Function g;
	
	public Product(Function f, Function g) {
		this.f = f;
		this.g = g;		
	}
	
	@Override
	public double apply(double value) {
		return f.apply(value) * g.apply(value);
	}
	
	@Override
	public Function derivative() {
		return new Sum(new Product(f.derivative(), g), new Product(f, g.derivative()));
	}
	
	@Override
	public String toString() {
		return f.toString() + " * " + g.toString();
	}
}