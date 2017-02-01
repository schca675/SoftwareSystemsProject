package testing;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.junit.Before;
import org.junit.Test;

import exc.IllegalBoardConstructorArgumentsException;
import exc.IllegalCoordinatesException;
import model.Board;
import model.TowerCoordinates;

public class BoardTest {
	
	public static final int LENGTH = 5;
	public static final int WIDTH = 7;
	public static final int HEIGHT = 6;
	public static final int WIN = 5; 
	public static final int UNLIMITED = Board.UNLIMITED_Z;
	public static final Integer PLAYER1 = 1;
	public static final Integer PLAYER2 = 2;
	
	/**
	 * Testing variables for default board.
	 * Assuming the default board has equal X-,Y-,Z- and Winning-length.
	 */
	/*@ requires Board.DEFAULT_XDIM == Board.DEFAULT_YDIM 
	  @ == Board.DEFAULT_ZDIM == Board.DEFAULT_WIN;  */
	public static final int MIN = 1;
	public static final int MAX = Board.DEFAULT_DIM;
	//@ requires Board.DEFAULT_DIM > 1;
	public static final int BET = Board.DEFAULT_DIM - 1;
	public static final int TOLOW = 0;
	public static final int TOHIGH = Board.DEFAULT_DIM + 1;
	
	private Board board;
	private Board specialBoard;
	private Board unlimitedBoard;
	
	/**
	 * Setup to test the Board.
	 */
	@Before
	public void setUp() {
		board = new Board();
		try {
			specialBoard = new Board(LENGTH, WIDTH, HEIGHT, WIN);
			unlimitedBoard = new Board(LENGTH, WIDTH, UNLIMITED, WIN);
		} catch (IllegalBoardConstructorArgumentsException e) {
			System.out.println(e.getMessage());
		}
	}

	// <------ Test the constructors ------>
	
	/**
	 * Test the Board constructor with default dimensions.
	 */
	@Test
	public void testDefaultDimension() {
		assertEquals(Board.DEFAULT_DIM, board.xDim);
		assertEquals(Board.DEFAULT_DIM, board.yDim);
		assertEquals(Board.DEFAULT_DIM, board.zDim);
		assertEquals(Board.DEFAULT_WIN, board.winningLength);
	}

	/**
	 * Test the Board Constructor with special dimensions.
	 */
	@Test
	public void testSpecialDimension() {
		assertEquals(LENGTH, specialBoard.xDim);
		assertEquals(WIDTH, specialBoard.yDim);
		assertEquals(HEIGHT, specialBoard.zDim);
		assertEquals(WIN, specialBoard.winningLength);
		assertEquals(UNLIMITED, unlimitedBoard.zDim);
	}
	
	// <------ Test the queries ------>
	
	/**
	 * Test the query CheckMove().
	 */
	@Test 
	public void testIsvalidMove() {
		assertTrue(board.isValidMove(MIN, MIN));
		assertTrue(board.isValidMove(MAX, MAX));
		assertTrue(board.isValidMove(BET, BET));
		assertFalse(board.isValidMove(TOLOW, TOLOW));
		assertFalse(board.isValidMove(TOLOW, BET));
		assertFalse(board.isValidMove(BET, TOLOW));
		assertFalse(board.isValidMove(TOHIGH, TOHIGH));
		assertFalse(board.isValidMove(TOHIGH, BET));
		assertFalse(board.isValidMove(BET, TOHIGH));	
		assertTrue(specialBoard.isValidMove(LENGTH, WIDTH));
		assertTrue(specialBoard.isValidMove(MIN, WIDTH));
		assertTrue(specialBoard.isValidMove(LENGTH, MIN));
		assertFalse(specialBoard.isValidMove(LENGTH + 1, WIDTH));
		assertFalse(specialBoard.isValidMove(LENGTH, WIDTH + 1));
	}
	
	/**
	 * Test of the isValidTower method with the default board.
	 */
	@Test
	public void testisValidTowerDef() {
		assertTrue(board.isValidTower(MIN, MIN));
		assertTrue(board.isValidTower(MIN, BET));
		assertTrue(board.isValidTower(BET, MIN));
		assertTrue(board.isValidTower(MAX, MAX));
		assertTrue(board.isValidTower(MAX, BET));
		assertTrue(board.isValidTower(BET, MAX));
		assertFalse(board.isValidTower(TOLOW, TOLOW));
		assertFalse(board.isValidTower(TOLOW, MIN));
		assertFalse(board.isValidTower(BET, TOLOW));
		assertFalse(board.isValidTower(TOHIGH, BET));
		assertFalse(board.isValidTower(MAX, TOHIGH));
		assertFalse(board.isValidTower(TOHIGH, TOHIGH));		
	}
	
	/**
	 * Test of the isValidTower method of a board with specific dimensions.
	 */
	@Test
	public void testisValidTowerSpec() {		
		assertTrue(specialBoard.isValidTower(5, 7));
		assertFalse(specialBoard.isValidTower(6, 5));
		assertFalse(specialBoard.isValidTower(3, 8));
	}
	
	/**
	 * Test of the isValidCell() method.
	 */
	@Test
	public void testisValidCell() {
		assertTrue(board.isValidCell(MIN, MIN, MIN));
		assertTrue(board.isValidCell(MAX, MIN, MIN));
		assertTrue(board.isValidCell(MIN, MAX, MIN));
		assertTrue(board.isValidCell(MIN, MIN, MAX));
		assertTrue(board.isValidCell(MAX, MAX, MAX));
		assertTrue(board.isValidCell(BET, BET, BET));
		assertFalse(board.isValidCell(MIN, MIN, -MIN));
		assertFalse(board.isValidCell(MIN, -MIN, MIN));
		assertFalse(board.isValidCell(-MIN, MIN, MIN));
		assertFalse(board.isValidCell(-MIN, -MIN, -MIN));
		assertFalse(board.isValidCell(TOHIGH, MIN, MIN));
		assertFalse(board.isValidCell(MIN, TOHIGH, MIN));
		assertFalse(board.isValidCell(MIN, MIN, TOHIGH));
		assertTrue(unlimitedBoard.isValidCell(MIN, MIN, 40));
	}
	
	/**
	 *  Test X - dimension for every Y and every Z layer.
	 */
	@Test 
	public void testHasWonXDir() {
		try {
			for (int z = MIN; z <= MAX; z++) {
				for (int y = MIN; y <= MAX; y++) {
					for (int x = MIN; x <= MAX; x++) {
						board.makeMove(x, y, PLAYER2);
					}
					for (int i = MIN; i <= MAX; i++) {
						assertTrue(board.hasWon(i, y));
					}
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X.");
		}
	}
	
	/**
	 * Test X direction has not won if there are different IDs.
	 */
	@Test
	public void testHasNotWonXDir() {
		Integer playerID = PLAYER2;
		try {
			for (int i = MIN; i <= MAX; i++) {
				board.makeMove(i, MIN, playerID);
				playerID = PLAYER1;
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X.");
		}
	}
	
	/**
	 *  Test Y - dimension for every X and every Z layer.
	 */
	@Test 
	public void testHasWonYDir() {
		try {
			for (int z = MIN; z <= MAX; z++) {
				for (int x = MIN; x <= MAX; x++) {
					for (int y = MIN; y <= MAX; y++) {
						board.makeMove(x, y, PLAYER2);
					}
					for (int i = 1; i <= 4; i++) {
						assertTrue(board.hasWon(x, i));
					}
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing Y.");
		}
	}
	
	/**
	 * Test Y direction has not won if there are different IDs.
	 */
	@Test
	public void testHasNotWonYDim() {
		Integer playerID = PLAYER2;
		try {
			for (int i = MIN; i <= MAX; i++) {
				board.makeMove(MIN, i, playerID);
				playerID = PLAYER1;
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing Y.");
		}
	}
	
	/**
	 *  Test Z - dimension for every X and every Y layer.
	 */
	@Test 
	public void testHasWonZDir() {
		try {
			for (int x = MIN; x <= MAX; x++) {
				for (int y = MIN; y <= MAX; y++) {
					for (int z = MIN; z <= MAX; z++) {
						board.makeMove(x, y, PLAYER2);
					}
					for (int i = MIN; i <= MAX; i++) {
						assertTrue(board.hasWon(x, y));
					}
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing Z.");
		}
	}
	
	/**
	 * Test Z direction has not won if there are different IDs.
	 */
	@Test 
	public void testHasNotWonZDim() {
		Integer playerID = PLAYER2;
		try {
			for (int i = MIN; i <= MAX; i++) {
				board.makeMove(MIN, i, playerID);
				playerID = PLAYER1;
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing Z.");
		}
	}
	
	/**
	 *  Test X+Y-direction for every Z-Layer
	 *  One possible winning diagonal per layer.
	 */
	@Test 
	public void testHasWonXpYDir() {
		try {
			for (int z = MIN; z <= MAX; z++) {
				for (int i = MIN; i <= MAX; i++) {
					board.makeMove(i, i, PLAYER2);
				}
				for (int j = MIN; j <= MAX; j++) {
					assertTrue(board.hasWon(j, j));
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X+Y.");
		}
	}
	
	/**
	 * Test X+Y direction has not won if there are different IDs.
	 */
	@Test
	public void testHasNotWonXpYDir() {
		Integer playerID = PLAYER2;
		try {
			for (int i = MIN; i <= MAX; i++) {
				board.makeMove(i, i, playerID);
				playerID = PLAYER1;
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X+Y.");
		}
	}
	
	/**
	 *  Test X-Y-direction for every Z-Layer
	 *  One possible winning diagonal per layer.
	 */
	@Test 
	public void testHasWonXmYDir() {		
		try {
			for (int z = MIN; z <= MAX; z++) {
				for (int i = 0; i < MAX; i++) {
					board.makeMove(MAX - i, MIN + i, PLAYER2);
				}
				for (int j = 0; j < MAX; j++) {
					assertTrue(board.hasWon(MAX - j, MIN + j, z));
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X-Y.");
		}
	}
	
	/**
	 * Test X-Y direction has not won if there are different IDs.
	 */
	@Test
	public void testHasNotWonXmYDir() {
		try {
			Integer playerID = PLAYER2;
			for (int i = 0; i < MAX; i++) {
				board.makeMove(MAX - i, MIN + i, playerID);
				playerID = PLAYER1;
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X-Y.");
		}
	}
	
	/**
	 * Test X+Z-direction for every Y-Layer.
	 * One possible winning diagonal per layer.
	 */
	@Test 
	public void testHasWonXpZDir() {
		try {
			for (int y = MIN; y <= MAX; y++) {
				for (int x = MIN; x <= MAX; x++) {
					for (int z = MIN; z <= x; z++) {
						board.makeMove(x, y, PLAYER2);
					}
				}
				for (int i = MIN; i <= MAX; i++) {
					assertTrue(board.hasWon(i, y));
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X+Z.");
		}
	}
	
	/**
	 * Test X+Z direction has not won if there are different IDs.
	 */
	@Test
	public void testHasNotWonXpZDir() {
		try {
			Integer playerID = PLAYER2;
			for (int x = MIN; x <= MAX; x++) {
				for (int z = MIN; z <= x; z++) {
					board.makeMove(x, MIN, playerID);
					playerID = PLAYER1;
				}
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X+Z.");
		}
	}
	
	/**
	 * Test X-Z-direction for every Y-Layer.
	 * One possible winning diagonal per layer.
	 */
	@Test 
	public void testHasWonXmZDir() {
		try {
			for (int y = MIN; y <= MAX; y++) {
				for (int x = MIN; x <= MAX; x++) {
					for (int z = MAX; z >= x; z--) {
						board.makeMove(x, y, PLAYER2);
					}
				}
				for (int i = MIN; i <= MAX; i++) {
					assertTrue(board.hasWon(i, y, MAX + 1 - i));
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X-Z.");
		}
	}
	
	/**
	 * Test X-Z direction has not won if there are different IDs.
	 */
	@Test
	public void testHasNotWonXmZDir() {
		try {
			Integer playerID = PLAYER2;
			for (int x = MIN; x <= MAX; x++) {
				for (int z = MAX; z >= x; z--) {
					board.makeMove(x, MIN, playerID);
					if (playerID == PLAYER2) {
						playerID = PLAYER1;
					} else {
						playerID = PLAYER2;
					}
				}
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X-Z.");
		}
	}
	
	/**
	 * Test Y+Z-direction for every X layer.
	 */
	@Test 
	public void testHasWonYpZDir() {
		try {
			for (int x = MIN; x <= MAX; x++) {
				for (int y = MIN; y <= MAX; y++) {
					for (int z = MIN; z <= y; z++) {
						board.makeMove(x, y, PLAYER1);
					}
				}
				for (int i = MIN; i <= MAX; i++) {
					assertTrue(board.hasWon(x, i, i));
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing Y+Z.");
		}
			
	}
	
	/**
	 * Test Y+Z direction has not won if there are different IDs.
	 */
	@Test
	public void testHasNotWonYpZDir() {
		try {
			Integer playerID = PLAYER2;
			for (int y = MIN; y <= MAX; y++) {
				for (int z = MIN; z <= y; z++) {
					board.makeMove(MIN, y, playerID);
					if (playerID == PLAYER2) {
						playerID = PLAYER1;
					} else {
						playerID = PLAYER2;
					}
				}
			}
			assertFalse(board.hasWon(MIN, 1, 1));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing Y+Z.");
		}
	}
	
	/**
	 * Test Y-Z-direction for every X layer.
	 */
	@Test 
	public void testHasWonYmZDir() {
		try {
			for (int x = MIN; x <= MAX; x++) {
				for (int y = MIN; y <= MAX; y++) {
					for (int z = MAX; z >= y; z--) {
						board.makeMove(x, y, PLAYER1);
					}
				}
				for (int i = MIN; i <= MAX; i++) {
					assertTrue(board.hasWon(x, i, MAX + 1 - i));
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing Y-Z.");
		}
	}
	
	/**
	 * Test Y-Z direction has not won if there are different IDs.
	 */
	@Test
	public void testHasNotWonYmZDir() {
		try {
			Integer playerID = PLAYER2;
			for (int y = MIN; y <= MAX; y++) {
				for (int z = MAX; z >= y; z--) {
					board.makeMove(MIN, y, playerID);
					if (playerID == PLAYER2) {
						playerID = PLAYER1;
					} else {
						playerID = PLAYER2;
					}
				}
			}
			assertFalse(board.hasWon(MIN, MIN, MAX));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing Y-Z.");
		}
	}
	
	/**
	 * Test X+Y+Z-direction.
	 */
	@Test 
	public void testHasWonXpYpZDir() {
		try {
			for (int x = MIN; x <= MAX; x++) {
				for (int z = MIN; z <= x; z++) {
					board.makeMove(x, x, PLAYER1);
				}
			}
			for (int i = MIN; i <= MAX; i++) {
				assertTrue(board.hasWon(i, i, i));
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X+Y+Z.");
		}	
	}
	
	/**
	 * Test X+Y+Z direction has not won if there are different IDs.
	 */
	@Test
	public void testHasNotWonXpYpZDir() {
		try {
			Integer playerID = PLAYER2;
			for (int x = MIN; x <= MAX; x++) {
				for (int z = MIN; z <= x; z++) {
					board.makeMove(x, x, playerID);
					if (playerID == PLAYER2) {
						playerID = PLAYER1;
					} else {
						playerID = PLAYER2;
					}
				}
			}
			assertFalse(board.hasWon(MIN, MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X+Y+Z.");
		}
	}
	
	/**
	 * Test X+Y-Z-direction.
	 */
	@Test 
	public void testHasWonXpYmZDir() {
		try {
			for (int x = MIN; x <= MAX; x++) {
				for (int z = MAX; z >= x; z--) {
					board.makeMove(x, x, PLAYER1);
				}
			}
			for (int i = MIN; i <= MAX; i++) {
				assertTrue(board.hasWon(i, i, MAX + 1 - i));
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X+Y-Z.");
		}	
	}
	
	/**
	 * Test X+Y-Z direction has not won if there are different IDs.
	 */
	@Test
	public void testHasNotWonXpYmZDir() {
		try {
			Integer playerID = PLAYER2;
			for (int x = MIN; x <= MAX; x++) {
				for (int z = MAX; z >= x; z--) {
					board.makeMove(x, x, playerID);
					if (playerID == PLAYER2) {
						playerID = PLAYER1;
					} else {
						playerID = PLAYER2;
					}
				}
			}
			assertFalse(board.hasWon(MIN, MIN, MAX));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X+Y-Z.");
		}
	}
	
	/**
	 * Test X-Y+Z-direction.
	 */
	@Test 
	public void testHasWonXmYpZDir() {
		try {
			for (int x = MIN; x <= MAX; x++) {
				for (int z = MIN; z <= x; z++) {
					board.makeMove(x, MAX + 1 - x, PLAYER1);
				}
			}
			for (int i = MIN; i <= MAX; i++) {
				assertTrue(board.hasWon(i, MAX + 1 - i, i));
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X-Y+Z.");
		}
	}
	
	/**
	 * Test X-Y+Z direction has not won if there are different IDs.
	 */
	@Test
	public void testHasNotWonXmYpZDir() {
		try {
			Integer playerID = PLAYER2;
			for (int x = MIN; x <= MAX; x++) {
				for (int z = MIN; z <= x; z++) {
					board.makeMove(x, MAX + 1 - x, playerID);
					if (playerID == PLAYER2) {
						playerID = PLAYER1;
					} else {
						playerID = PLAYER2;
					}
				}
			}
			assertFalse(board.hasWon(MIN, MAX, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X-Y+Z.");
		}
	}
	
	/**
	 * Test X-Y-Z-direction.
	 */
	@Test 
	public void testHasWonXmYmZDir() {
		try {
			for (int y = MIN; y <= MAX; y++) {
				for (int z = MIN; z <= y; z++) {
					board.makeMove(MAX + 1 - y, y, PLAYER1);
				}
			}
			for (int i = MIN; i <= MAX; i++) {
				assertTrue(board.hasWon(MAX + 1 - i, i, i));
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X-Y-Z.");
		}
	}
	
	/**
	 * Test X-Y-Z direction has not won if there are different IDs.
	 */
	@Test
	public void testHasNotWonXmYmZDir() {
		try {
			Integer playerID = PLAYER2;
			for (int y = MIN; y <= MAX; y++) {
				for (int z = MIN; z <= y; z++) {
					board.makeMove(MAX + 1 - y, y, playerID);
					if (playerID == PLAYER2) {
						playerID = PLAYER1;
					} else {
						playerID = PLAYER2;
					}
				}
			}
			assertFalse(board.hasWon(MIN, MAX, MAX));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing X-Y-Z.");
		}
	}
	
	/**
	 * Test the query isFull().
	 */
	@Test
	public void testisFull() {
		try {
			assertFalse(board.isFull());
			for (int i = MIN; i <= MAX; i++) {
				for (int j = MIN; j <= MAX; j++) {
					for (int k = MIN; k <= MAX; k++) {
						board.makeMove(i, j, PLAYER2);
					}
				}
			}
			assertTrue(board.isFull());	
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing isFull.");
		}		
	}
	
	/**
	 * Test the getAvailableTowers method.
	 */
	@Test
	public void testgetAvailableTowers1() {
		List<TowerCoordinates> data = board.getAvailableTowers();
		for (int i = 0; i < data.size(); i++) {
			assertTrue(board.isValidMove(data.get(i).getX(), data.get(i).getY()));
		}
		for (int x = MIN; x <= MAX; x++) {
			for (int y = MIN; y <= MAX; y++) {
				TowerCoordinates test = new TowerCoordinates(x, y);
				if (!data.contains(test)) {
					assertFalse(board.isValidMove(test.getX(), test.getY()));
				}
			}
		}
	}
	
	/**
	 * Test the getAvailableTowers method with first filling some towers.
	 */
	@Test
	public void testgetAvailableTowers2() {
		try {
			for (int i = 1; i <= MAX; i++) {
				for (int j = 1; j <= MAX; j++) {
					board.makeMove(i, i, PLAYER1);
	
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exception while testing testGetAvailableTowers2");
		}
		List<TowerCoordinates> data = board.getAvailableTowers();
		for (int i = 0; i < data.size(); i++) {
			assertTrue(board.isValidMove(data.get(i).getX(), data.get(i).getY()));
		}
		for (int x = MIN; x <= MAX; x++) {
			for (int y = MIN; y <= MAX; y++) {
				TowerCoordinates test = new TowerCoordinates(x, y);
				if (!data.contains(test)) {
					assertFalse(board.isValidMove(test.getX(), test.getY()));
				}
			}
		}
	}
	
	/**
	 * Test the deep copy method of the board.
	 * @throws IllegalCoordinatesException in case make Move gets invalid coordinates.
	 */
	@Test
	public void testDeepCopy() throws IllegalCoordinatesException {
		board.makeMove(MIN, MIN, PLAYER1);
		board.makeMove(MIN, MIN, PLAYER2);
		board.makeMove(MIN, MIN, PLAYER1);
		board.makeMove(MIN, MIN, PLAYER1);
		board.makeMove(MIN, MAX, PLAYER1);
		Board testBoard = board.deepCopy();
		assertEquals(testBoard.getCellOwner(MIN, MIN, 1), PLAYER1);
		assertEquals(testBoard.getCellOwner(MIN, MIN, 2), PLAYER2);
		assertEquals(testBoard.getCellOwner(MIN, MIN, 3), PLAYER1);
		assertEquals(testBoard.getCellOwner(MIN, MIN, 4), PLAYER1);
		assertEquals(testBoard.getCellOwner(MIN, MAX, 1), PLAYER1);
		testBoard.makeMove(BET, BET, PLAYER1);
		assertEquals(testBoard.getCellOwner(BET, BET, 1), PLAYER1);
		assertNotEquals(board.getCellOwner(BET, BET, 1), PLAYER1);
	}
	
	/**
	 * Test the deepdataCopy method of the board data.
	 * @throws IllegalCoordinatesException in case make Move gets invalid coordinates.
	 */
	@Test
	public void deepdataCopy() throws IllegalCoordinatesException {
		board.makeMove(MIN, MIN, PLAYER1);
		List<List<Integer>> data = board.deepDataCopy();
		assertEquals(data.get(0).get(0), PLAYER1);
	}
	
	/**
	 * Test the query GetCellOwner().
	 */
	@Test
	public void testGetCellOwner() {
		try {
			assertNull(board.getCellOwner(MIN, MIN, MIN));
			assertNull(board.getCellOwner(MIN, MIN, 0));
			board.makeMove(MIN, MIN, PLAYER2);
			assertEquals(board.getCellOwner(MIN, MIN, MIN), PLAYER2);	
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing GetCellOwner.");
		}
			
	}
	
	/**
	 * Test the query isEmptyCell().
	 */
	@Test
	public void testIsEmptyCell() {
		try {
			assertTrue(board.isEmptyCell(MIN, MIN, MIN));
			board.makeMove(MIN, MIN, PLAYER2);
			assertFalse(board.isEmptyCell(MIN, MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing IsEmptyCell.");
		}
		
	}
	
	/**
	 * Test the query getTowerHeight().
	 */
	@Test
	public void getTowerHeight() {
		try {
			assertEquals(0, board.getTowerHeight(MIN, MAX));
			board.makeMove(MIN, MAX, PLAYER2);
			assertEquals(1, board.getTowerHeight(MIN, MAX));
			board.makeMove(MIN, MAX, PLAYER2);
			assertEquals(2, board.getTowerHeight(MIN, MAX));
			board.makeMove(MIN, MAX, PLAYER2);
			assertEquals(3, board.getTowerHeight(MIN, MAX));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing getTowerHeight.");
		}
	}
	
	/**
	 * Test GetTower method.
	 */
	@Test
	public void testGetTower() {
		try {
			for (int x = MIN; x <= MAX; x++) {
				for (int y = MIN; y <= MAX; y++) {
					board.makeMove(x, y, PLAYER2);
					board.makeMove(x, y, PLAYER1);
					board.makeMove(x, y, PLAYER1);
					board.makeMove(x, y, PLAYER2);
					List<Integer> coords = board.getTower(x, y);
					assertEquals(coords.get(0), PLAYER2);
					assertEquals(coords.get(1), PLAYER1);
					assertEquals(coords.get(2), PLAYER1);
					assertEquals(coords.get(3), PLAYER2);
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println(e.getMessage());
			System.out.println("Make move broke");
		}		
	}
	
	/**
	 * Test the GetTowerCoordinates method.
	 */
	@Test
	public void testGetTowerCoordinates() {
		TowerCoordinates one1 = new TowerCoordinates(1, 1);
		assertEquals(one1, board.getTowerCoordinates(0));
		TowerCoordinates one2 = new TowerCoordinates(1, 2);
		assertEquals(one2, board.getTowerCoordinates(4));
		TowerCoordinates one3 = new TowerCoordinates(1, 3);
		assertEquals(one3, board.getTowerCoordinates(8));
		TowerCoordinates one4 = new TowerCoordinates(1, 4);
		assertEquals(one4, board.getTowerCoordinates(12));
		TowerCoordinates two1 = new TowerCoordinates(2, 1);
		assertEquals(two1, board.getTowerCoordinates(1));
		TowerCoordinates two2 = new TowerCoordinates(2, 2);
		assertEquals(two2, board.getTowerCoordinates(5));
		TowerCoordinates two3 = new TowerCoordinates(2, 3);
		assertEquals(two3, board.getTowerCoordinates(9));
		TowerCoordinates two4 = new TowerCoordinates(2, 4);
		assertEquals(two4, board.getTowerCoordinates(13));
		TowerCoordinates three1 = new TowerCoordinates(3, 1);
		assertEquals(three1, board.getTowerCoordinates(2));
		TowerCoordinates three2 = new TowerCoordinates(3, 2);
		assertEquals(three2, board.getTowerCoordinates(6));
		TowerCoordinates three3 = new TowerCoordinates(3, 3);
		assertEquals(three3, board.getTowerCoordinates(10));
		TowerCoordinates three4 = new TowerCoordinates(3, 4);
		assertEquals(three4, board.getTowerCoordinates(14));
		TowerCoordinates four1 = new TowerCoordinates(4, 1);
		assertEquals(four1, board.getTowerCoordinates(3));
		TowerCoordinates four2 = new TowerCoordinates(4, 2);
		assertEquals(four2, board.getTowerCoordinates(7));
		TowerCoordinates four3 = new TowerCoordinates(4, 3);
		assertEquals(four3, board.getTowerCoordinates(11));
		TowerCoordinates four4 = new TowerCoordinates(4, 4);
		assertEquals(four4, board.getTowerCoordinates(15));
		
	}


	// <------ Test the commands ------>
	
	@Test
	public void testMakeMove() {
		try {
			board.makeMove(1, 1, PLAYER2);
			assertFalse(board.isEmptyCell(1, 1, 1));
			assertTrue(board.isEmptyCell(1, 1, 2));
			assertTrue(board.isEmptyCell(1, 1, 3));
			assertTrue(board.isEmptyCell(1, 1, 4));
			board.makeMove(1, 1, PLAYER2);
			assertEquals(board.getCellOwner(1, 1, 1), PLAYER2);
			assertEquals(board.getCellOwner(1, 1, 2), PLAYER2);
			assertNotEquals(board.getCellOwner(1, 1, 3), PLAYER2);
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing Make Move.");
		}
	}
	
//	/**
//	 * Test for the Reset() method, now private so can not be used to test.
//	 */
//	@Test
//	public void testReset() {
//		for (int i = 1; i <= 4; i++) {
//			for (int j = 1; j <= 4; j++) {
//				for (int k = 1; k <= 4; k++) {
//					assertTrue(board.isEmptyCell(i, j, k));
//				}
//			}
//		}
//		board.makeMove(1, 2, PLAYER2);
//		board.makeMove(1, 2, PLAYER2);
//		board.makeMove(1, 2, PLAYER2);	
//		board.makeMove(3, 2, PLAYER2);
//		board.makeMove(4, 2, PLAYER2);
//		board.reset();
//		for (int i = 1; i <= 4; i++) {
//			for (int j = 1; j <= 4; j++) {
//				for (int k = 1; k <= 4; k++) {
//					assertTrue(board.isEmptyCell(i, j, k));
//				}
//			}
//		}
//	}
	
	
}
