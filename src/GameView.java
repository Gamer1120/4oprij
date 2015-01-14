import java.util.Observer;

public interface GameView extends Observer {
	public void start(Game controller);

	public void command();

	public void printBoard(Board board);

	public int makeMove(String name);

	public void printResult(String name);
}
