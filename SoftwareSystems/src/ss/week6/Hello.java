package ss.week6;

import java.util.Scanner;

public class Hello {
	public static void main(String[] args) {
		Scanner scanny = new Scanner(System.in);
		boolean stop = false;
		while (!stop) {
			String print = scanny.next();
			scanny.hasNext();
			if (!print.isEmpty()) {
				System.out.println("Hello " + print);
			} else {
				stop = true;
			}
		}
	}
}
