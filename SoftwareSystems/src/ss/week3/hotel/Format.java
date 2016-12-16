package ss.week3.hotel;

public class Format {

	public static void printLine(String text, double amount) {
		String format = "%-20s%10.2f";
		String toprint = String.format(format, text, amount);
		System.out.println(toprint);
	}

	public static void main(String[] args) {
		printLine("text1", 1);
		printLine("other text", -12.12);
		printLine("something", 0.2);
	}
}
