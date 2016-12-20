package ss.week6;

import java.util.Scanner;

public class Words {
	public static void main(String[] args) {
		System.out.println("Line (or ''end''):");
		Scanner scanny = new Scanner(System.in);
		boolean stop = false;
		while (!stop && scanny.hasNext()) {
			String sentence = scanny.nextLine();
			if (!sentence.equals("end")) {
				System.out.println(sentence);
				Scanner stringscanny = new Scanner(sentence);
				int i = 1;
				while (stringscanny.hasNext()) {
					System.out.println("Word " + i + ": " + stringscanny.next());
					i = i + 1;
				}
				System.out.println("Line (or ''end'')");
				stringscanny.close();
			} else {
				stop = true;
				System.out.println("End of programme.");
				scanny.close();
			}
		}
	}

}
