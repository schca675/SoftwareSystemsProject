package ss.week4;

public class Sum implements Function, Integrandable {
	private Function f;
	private Function g;

	public Sum(Function f, Function g) {
		this.f = f;
		this.g = g;		
	}
	
	@Override
	public double apply(double value) {
		return f.apply(value) + g.apply(value);
	}

	@Override
	public Sum derivative() {
		return new Sum(f.derivative(), g.derivative());
	}
	
	// We could also test if f.integrand == null || g.integrand == null.
	@Override
	public Function integrand() {
		if (f instanceof Integrandable && g instanceof Integrandable) {
			return new Sum(((Integrandable) f).integrand(), ((Integrandable) g).integrand());
		} else {
			return null;
		}
	}
	
	@Override
	public String toString() {
		return f.toString() + " + " + g.toString();
	}
}
