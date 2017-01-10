package ss.week7.threads;

public class TestConsole extends Thread {

	@Override
	public void run() {
		sum();
	}
	
	private void sum() {
		int a = Console.readInt(this.getName() + ": " + "First number");
		int b = Console.readInt(this.getName() + ": " + "Second number");
		int sum = a + b;
		Console.println(this.getName() + ": " + a + " + " + b + " = " + sum);
	}
	
	public static void main (String[] args) {
		TestConsole a = new TestConsole();
		TestConsole b = new TestConsole();
		a.start();
		b.start();
	}
}
