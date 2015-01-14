import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Observable;

public class GameTUIView implements GameView {
	public final static String PLAY = "PLAY";
	public final static String RESET = "RESET";
	public final static String EXIT = "EXIT";
	public final static String HELP = "HELP";

	private Game game;

	@Override
	public void start(Game controller) {
		game = controller;
		command();
	}

	@Override
	public void command() {
		BufferedReader reader = new BufferedReader(new InputStreamReader(
				System.in));
		while (true) {
			System.out.println("Please input command");
			try {
				String line = reader.readLine();
				switch (line) {
				case PLAY:
					game.play();
					break;
				case RESET:
					game.reset();
					break;
				case EXIT:
					System.exit(0); //TODO: beter afsluiten
					break;
				case HELP:
					System.out.println("Please input command"); //TODO: betere help
					break;
				default:
					System.out.println("Invalid command");
					break;
				}
			} catch (IOException | NullPointerException e) {
				e.printStackTrace();
			}
		}
	}

	@Override
	public void update(Observable o, Object arg) {
		System.out.println(arg);

	}

	@Override
	public void printBoard(Board board) {
		System.out.println(board);
	}

	@Override
	public int makeMove(String name) {
		BufferedReader reader = new BufferedReader(new InputStreamReader(
				System.in));
		while (true) {
			System.out.println(name + " input your move or a command");
			try {
				String line = reader.readLine();
				switch (line) {
				case RESET:
					game.reset();
					game.play();
					break;
				case EXIT:
					System.exit(0); //TODO: beter afsluiten
					break;
				case HELP:
					System.out.println("Please input move or command"); //TODO: betere help
					break;
				default:
					try {
						return Integer.parseInt(line);
					} catch (NumberFormatException ex) {
						System.out.println("Invalid input");
					}
					break;
				}

			} catch (IOException | NullPointerException e) {
				e.printStackTrace();
			}
		}
	}

	@Override
	public void printResult(String name) {
		if (name != null) {
			System.out.println(name + " won!");
		} else {
			System.out.println("Draw");
		}
		command();
	}
}
