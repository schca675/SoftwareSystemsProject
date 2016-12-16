package ss.week3.hotel;

public class Bill {
	private double sum;
	private java.io.PrintStream printStream;
	private String format = "%-20s%10.2f";

	public interface Item {
		double getAmount();

		String toString();
	}	

	public Bill(java.io.PrintStream theOutStream) {
		sum = 0;
		printStream = theOutStream;
	}

	/**
	 * Print the sum of the bill on the output stream.
	 */
	public void close() {
		String toPrint = String.format(format, "Total:", sum);
		printStream.println(toPrint);
	}

	/**
	 * Returns the sum of the Bill.
	 * 
	 * @return the sum of the bill.
	 */
	public double getSum() {
		return sum;
	}

	/**
	 * Add an item to the Bill. If there is an output, the item will be printed
	 * on this output and the amount will be added to the sum of the Bill
	 * 
	 * @param theOutStream
	 */
	public void newItem(Bill.Item item) {
		double amount = item.getAmount();
		String description = item.toString();
		sum = sum + amount;
		String toPrint = String.format(format, description, amount);
		//add if
		printStream.println(toPrint); 
	}

}
