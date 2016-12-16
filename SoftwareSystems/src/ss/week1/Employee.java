package ss.week1;

public class Employee {

	private int hours;
	private double rate;

	public double paid() {
		if (hours > 40) {
			return 40 * rate + (hours - 40) * 1.5 * rate;
		} else {
			return hours * rate;
		}

	}

}
