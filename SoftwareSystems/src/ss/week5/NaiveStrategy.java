package ss.week5;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import ss.week5.TicTacToe.Board;
import ss.week5.TicTacToe.Mark;

public class NaiveStrategy implements Strategy {
	public String getName() {
		return "Naive";
	}
	
	public int determineMove(Board b, Mark m) {
		List<Integer> emptyList = new ArrayList<>();
		int dim = Board.DIM * Board.DIM;
		for (int i = 0; i < dim; i++) {
			if (b.isEmptyField(i)) {
				emptyList.add(i);
			}
		}		
		Random random = new Random();
		return emptyList.get(random.nextInt(emptyList.size()));
	}
}
