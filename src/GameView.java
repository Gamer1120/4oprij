import java.util.Observer;

public interface GameView extends Observer {
	public void start();

	public void play();

	public void update(Board board);

	public int makeMove(Player player);

	public void printResult(Player player);
}
