package ss.week7.threads;

public class TestSyncConsole extends Thread {
	@Override
	public void run() {
		sum();
	}
	
	private synchronized void sum() {
		int a = SyncConsole.readInt(this.getName() + ": " + "First number");
		int b = SyncConsole.readInt(this.getName() + ": " + "Second number");
		int sum = a + b;
		SyncConsole.println(this.getName() + ": " + a + " + " + b + " = " + sum);
	}
	
	public static void main(String[] args) {
		TestConsole a = new TestConsole();
		TestConsole b = new TestConsole();
		a.start();
		b.start();
	}
}
